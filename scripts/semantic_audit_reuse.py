#!/usr/bin/env python3
"""Fail-closed item-level reuse for v10 statement and coverage sidecars.

This helper is deliberately narrower than a semantic audit.  It never infers
that a source claim and Lean declaration match.  Instead, it can carry an
already-reviewed v10 item over a map/cache refresh only after all of the
following are independently pinned:

* the source item's semantic digest and byte-anchored quote identity;
* every elaborated manifest atom's ref, role, binder information, and
  canonical structure; and
* the complete Lean-owned transitive proposition/constant dependency graph,
  including exact artifacts only for opaque imported terminals whose bodies
  are unavailable to that graph; and
* the scoped operational semantic-review protocol digest;
* corrected-target or source-model-convention disposition pins.

Names, map keys, source locations, declaration names, and raw pretty-printed
Lean spelling are navigation or trace evidence only. They may be rewritten
after the content identities match uniquely, but never select a candidate on
their own. The default command is a dry run. ``--write``
updates only individually accepted entries and leaves every rejected entry
untouched for a fresh audit.

Legacy sidecars normally lack the historical source/manifest identities needed
to refresh a changed manifest serializer.  Supply both ``--previous-source-map``
and ``--previous-review-cache`` once, or first create the entry-local
``semantic_reuse_v1`` pins during a fully current v10 audit.  Missing evidence
is a rejection, not a name-based fallback.  The explicit
``--bootstrap-current`` mode records those pins only after the current v10
ledger and routes validate; it is not a stale-evidence override.

The older ``paper-coverage-v4-semantic-proof-and-pinned-defect-support``
format did not save per-row Lean signature pins.  It is therefore never
silently refreshed.  The separate ``--migrate-legacy-v4-coverage`` operation
is an all-or-nothing conversion to the current statement-v10/coverage-v5
contract.  It needs both pre-change snapshots, reconstructs each legacy source
item from its exact statement digest, and accepts a linked row only after both
old and current elaborated signatures and a name-independent manifest
structure are verified.  Row/source names locate snapshot records; they do
not establish an identity.
"""

from __future__ import annotations

import argparse
import copy
import hashlib
import json
import re
import sys
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Callable, Iterable, Mapping, Sequence


ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts import review_dashboard  # noqa: E402
from scripts.formalization_protocol import (  # noqa: E402
    FORMALIZATION_REVIEW_PROTOCOL_FIELD,
    formalization_protocol_receipt_matches,
    formalization_review_protocol_digest,
)
from scripts.lean_signature_manifest import (  # noqa: E402
    normalize_signature_manifest,
    semantic_dependency_manifest,
    signature_manifest_digest,
)
from scripts.source_coverage_scope import (  # noqa: E402
    SOURCE_ITEM_COVERAGE_DIGEST_SCHEMA,
    filter_source_inventory_for_coverage,
    source_coverage_mode_from_map,
    source_coverage_modes_compatible,
    source_item_coverage_sha256,
    source_named_result_environment_kinds_from_map,
)
from scripts.source_record_target_disposition import (  # noqa: E402
    model_convention_semantic_digest,
)
from scripts.source_map_inventory import inventory_from_source_map  # noqa: E402


REUSE_SCHEMA = 2
ENTRY_REUSE_SCHEMA = 3
REVIEW_VALIDATOR_IDENTITY_SCHEMA = 1
# Keep the historical field label so existing sidecars can fail closed on the
# embedded schema instead of losing their migration metadata by field rename.
REUSE_FIELD = "semantic_reuse_v1"
COVERAGE_SEMANTIC_EXCLUSION = "authenticated_outside_canonical_coverage"
LEGACY_V4_COVERAGE_PROMPT_VERSION = (
    "paper-coverage-v4-semantic-proof-and-pinned-defect-support"
)
LEGACY_V4_MIGRATION_FIELD = "legacy_v4_coverage_migration_v1"
LEGACY_V4_MIGRATION_SCHEMA = 1
SHA256_RE = re.compile(r"^[0-9a-f]{64}$", re.IGNORECASE)
ROUTE_NAVIGATION_FIELDS = frozenset(
    {
        "source_item",
        "source_location",
        "archival_source_location",
    }
)
MODEL_CONVENTION_IDS_FIELD = "model_convention_ids"
SOURCE_MODEL_CONVENTION_PINS_FIELD = "source_model_convention_pins"
STRUCTURED_MODEL_CONVENTION_STATUSES = frozenset(
    {
        "documented_model_convention",
        "documented_source_domain_convention",
        "documented_source_model_convention",
        "source_model_convention",
    }
)
MODEL_CONVENTION_REQUIRED_FIELDS = (
    "source_locator",
    "classification",
    "formal_meaning",
    "why_needed",
    "checked_scope",
)
LEGACY_V4_DIRECT_COVERAGE_JUDGMENTS = frozenset(
    {
        "covered",
        "covered_by_rows",
        "conditional_boundary",
        "covered_with_boundary",
        review_dashboard.CORRECTED_TARGET_COVERAGE,
    }
)


def _stable_digest(value: object) -> str:
    return hashlib.sha256(
        json.dumps(
            value,
            ensure_ascii=False,
            sort_keys=True,
            separators=(",", ":"),
            default=str,
        ).encode("utf-8")
    ).hexdigest()


def _sha256_text(value: str) -> str:
    return hashlib.sha256(value.encode("utf-8")).hexdigest()


def _valid_digest(value: object) -> str:
    text = str(value or "").strip().lower()
    return text if SHA256_RE.fullmatch(text) else ""


def _string_list(value: object) -> list[str]:
    if isinstance(value, (list, tuple, set)):
        values = value
    elif value is None:
        values = []
    else:
        values = [value]
    return [str(item).strip() for item in values if str(item).strip()]


def canonical_coverage_inventory_projection(
    folder: Path,
    *,
    current_inventory: Mapping[str, Mapping[str, Any]],
    current_mode: str,
) -> tuple[dict[str, Mapping[str, Any]], str]:
    """Project the canonical closeout coverage selection onto reuse inventory.

    Statement reuse needs the complete source map because a reviewed Lean row
    may cite model or proof-support material outside ordinary paper coverage.
    Coverage reuse must instead use the exact source-first subset selected by
    the dashboard.  Projecting the selector's keys back onto the reuse
    inventory keeps both lanes on the same source payload without treating a
    sidecar key as evidence that an item belongs in coverage scope.
    """

    structural_errors = review_dashboard.paper_source_map_structural_errors(folder)
    if structural_errors:
        return {}, (
            "canonical coverage source map failed structural validation before "
            "selection or exclusion pruning: " + "; ".join(structural_errors)
        )

    canonical_full, canonical_selected, canonical_mode, mode_error = (
        review_dashboard.paper_coverage_inventory(folder)
    )
    if mode_error:
        return {}, f"canonical coverage selector failed: {mode_error}"
    if canonical_mode != current_mode:
        return {}, (
            "canonical coverage selector mode disagrees with the current "
            f"source map: {canonical_mode!r} != {current_mode!r}"
        )
    current_keys = set(current_inventory)
    canonical_keys = set(canonical_full)
    if current_keys != canonical_keys:
        return {}, (
            "canonical coverage selector/full-inventory projection mismatch: "
            f"missing={sorted(canonical_keys - current_keys)}, "
            f"unexpected={sorted(current_keys - canonical_keys)}"
        )
    for key in sorted(current_keys):
        current_item = current_inventory.get(key)
        canonical_item = canonical_full.get(key)
        if not isinstance(current_item, Mapping) or not isinstance(
            canonical_item, Mapping
        ):
            return {}, (
                "canonical coverage selector/full-inventory projection mismatch "
                f"at {key!r}: source item is not an object"
            )
        current_target = review_dashboard._source_item_coverage_statement(
            dict(current_item)
        )[1]
        canonical_target = review_dashboard._source_item_coverage_statement(
            dict(canonical_item)
        )[1]
        if not current_target or current_target != canonical_target:
            return {}, (
                "canonical coverage selector/full-inventory projection mismatch "
                f"at {key!r}: semantic coverage target changed"
            )
    selected_keys = set(canonical_selected)
    if not selected_keys.issubset(current_keys):
        return {}, (
            "canonical coverage selector returned items outside the current "
            f"source inventory: {sorted(selected_keys - current_keys)}"
        )
    return {key: current_inventory[key] for key in canonical_selected}, ""


def source_anchor_quote_identity(item: Mapping[str, Any]) -> tuple[str, str]:
    """Return a content-only identity for exact self-hashed source quotes.

    Paths and line ranges are deliberately left out because an unchanged source
    passage can move after an unrelated edit.  The caller must separately run
    the current byte-anchor validator before accepting this identity.
    """

    anchors = item.get("source_anchor_evidence")
    if not isinstance(anchors, list) or not anchors:
        return "", "source item has no source_anchor_evidence"
    quote_digests: list[str] = []
    for index, raw_anchor in enumerate(anchors):
        if not isinstance(raw_anchor, Mapping):
            return "", f"source anchor {index} is not an object"
        quote = raw_anchor.get("quoted_text")
        recorded = _valid_digest(raw_anchor.get("quoted_text_sha256"))
        if not isinstance(quote, str) or not quote:
            return "", f"source anchor {index} has no quoted_text"
        normalized = quote.replace("\r\n", "\n").replace("\r", "\n")
        actual = _sha256_text(normalized)
        if not recorded or recorded != actual:
            return "", f"source anchor {index} quoted_text_sha256 is stale"
        quote_digests.append(actual)
    return _stable_digest({"schema": 1, "quotes": quote_digests}), ""


def _model_convention_ids(item: Mapping[str, Any]) -> tuple[list[str] | None, str]:
    """Read only explicit structured convention dependencies.

    Free-form notes are evidence for a human reviewer, not a dependency
    declaration.  Their wording must neither create nor suppress a convention
    pin; absence of the structured field means that no convention is cited.
    """

    declared = MODEL_CONVENTION_IDS_FIELD in item
    raw_ids = item.get(MODEL_CONVENTION_IDS_FIELD)
    structured_status = str(item.get("source_status") or "").strip().lower()
    if not declared:
        if structured_status in STRUCTURED_MODEL_CONVENTION_STATUSES:
            return (
                None,
                "structured source-model-convention status requires nonempty "
                f"{MODEL_CONVENTION_IDS_FIELD}",
            )
        return [], ""
    if not isinstance(raw_ids, list):
        return None, f"source-map {MODEL_CONVENTION_IDS_FIELD} must be a nonempty list of unique strings"
    ids = [value.strip() for value in raw_ids if isinstance(value, str) and value.strip()]
    if len(ids) != len(raw_ids) or not ids or len(set(ids)) != len(ids):
        return None, f"source-map {MODEL_CONVENTION_IDS_FIELD} must be a nonempty list of unique strings"
    return sorted(ids), ""


def _canonical_model_convention_index(
    source_proof_fidelity: Mapping[str, Any] | None,
) -> tuple[dict[str, Mapping[str, Any]], str]:
    """Index canonical source-proof convention records by their explicit IDs."""

    if not isinstance(source_proof_fidelity, Mapping):
        return {}, "canonical source-proof-fidelity ledger is unavailable"
    raw_conventions = source_proof_fidelity.get("model_conventions")
    if not isinstance(raw_conventions, list):
        return {}, "source-proof-fidelity model_conventions must be a list"
    conventions: dict[str, Mapping[str, Any]] = {}
    for index, raw_convention in enumerate(raw_conventions):
        if not isinstance(raw_convention, Mapping):
            return {}, f"source-proof-fidelity model_conventions[{index}] is not an object"
        convention_id = str(raw_convention.get("id") or "").strip()
        if not convention_id:
            return {}, f"source-proof-fidelity model_conventions[{index}] has no id"
        if convention_id in conventions:
            return (
                {},
                f"source-proof-fidelity model_conventions duplicates id `{convention_id}`",
            )
        for field in MODEL_CONVENTION_REQUIRED_FIELDS:
            if not str(raw_convention.get(field) or "").strip():
                return (
                    {},
                    f"source-proof-fidelity model convention `{convention_id}` lacks `{field}`",
                )
        conventions[convention_id] = raw_convention
    return conventions, ""


def source_model_convention_pins(
    item: Mapping[str, Any],
    *,
    source_proof_fidelity: Mapping[str, Any] | None,
) -> tuple[dict[str, Any] | None, str]:
    """Pin cited convention records or reject an unbound convention claim.

    The resulting digest map binds the *complete* canonical ledger records. A
    source-map ID therefore cannot retain reuse after its source meaning,
    approval, or checked scope changes.  IDs are sorted because their order is
    not a semantic claim; every listed convention remains independently bound.
    """

    ids, ids_error = _model_convention_ids(item)
    if ids is None:
        return None, ids_error
    if not ids:
        return {}, ""
    conventions, ledger_error = _canonical_model_convention_index(source_proof_fidelity)
    if ledger_error:
        return None, ledger_error
    digests: dict[str, str] = {}
    for convention_id in ids:
        record = conventions.get(convention_id)
        if record is None:
            return (
                None,
                "source-map "
                f"{MODEL_CONVENTION_IDS_FIELD} cites unknown canonical "
                f"source-proof-fidelity convention id `{convention_id}`",
            )
        digests[convention_id] = model_convention_semantic_digest(record)
    return {
        "schema": REUSE_SCHEMA,
        MODEL_CONVENTION_IDS_FIELD: ids,
        "record_sha256_by_id": digests,
    }, ""


def corrected_or_convention_pin(item: Mapping[str, Any]) -> dict[str, Any]:
    """Pin source disposition fields which must not be refreshed by a rename."""

    target = review_dashboard._source_item_corrected_target(dict(item))
    if target is None:
        return {
            "kind": "ordinary_or_convention",
            "source_kind": str(item.get("source_kind") or "").strip().lower(),
            "source_status": str(item.get("source_status") or "").strip().lower(),
            "coverage_status": str(item.get("coverage_status") or "").strip().lower(),
            "protocol_role": str(item.get("protocol_role") or "").strip().lower(),
        }
    approval = target.get("approval")
    approval = approval if isinstance(approval, Mapping) else {}
    return {
        "kind": "approved_corrected_target",
        "archival_statement_sha256": _valid_digest(item.get("statement_sha256")),
        "corrected_target_sha256": _valid_digest(target.get("corrected_target_sha256")),
        "governing_defect_ids": sorted(_string_list(target.get("governing_defect_ids"))),
        "approval_artifact_sha256": _valid_digest(approval.get("artifact_sha256")),
        "archival_equivalence_claimed": target.get("archival_equivalence_claimed"),
        "source_kind": str(item.get("source_kind") or "").strip().lower(),
        "source_status": str(item.get("source_status") or "").strip().lower(),
        "coverage_status": str(item.get("coverage_status") or "").strip().lower(),
    }


def source_reuse_pin(
    item: Mapping[str, Any],
    mode: str,
    *,
    source_proof_fidelity: Mapping[str, Any] | None = None,
) -> tuple[dict[str, Any] | None, str]:
    """Return one source identity used by statement and coverage reuse."""

    semantic_digest = source_item_coverage_sha256(dict(item), mode)
    quote_identity, quote_error = source_anchor_quote_identity(item)
    statement, target_digest = review_dashboard._source_item_coverage_statement(dict(item))
    if not semantic_digest:
        return None, "source item has no semantic digest"
    if quote_error:
        return None, quote_error
    if not statement or not _valid_digest(target_digest):
        return None, "source item has no canonical coverage statement"
    convention_pins, convention_error = source_model_convention_pins(
        item, source_proof_fidelity=source_proof_fidelity
    )
    if convention_pins is None:
        return None, convention_error
    disposition = corrected_or_convention_pin(item)
    if disposition.get("kind") == "approved_corrected_target" and not all(
        (
            disposition.get("corrected_target_sha256"),
            disposition.get("governing_defect_ids"),
            disposition.get("approval_artifact_sha256"),
            disposition.get("archival_equivalence_claimed") is False,
        )
    ):
        return None, "corrected target has incomplete correction/convention pins"
    pin: dict[str, Any] = {
        "schema": REUSE_SCHEMA,
        "source_item_semantic_sha256": semantic_digest,
        "source_anchor_quote_identity_sha256": quote_identity,
        "source_target_sha256": target_digest,
        "source_target_disposition": disposition,
    }
    # Omit the empty field so already-pinned ordinary items keep their exact
    # identity after this hardening.  Convention-bound items carry the full
    # canonical record digests above.
    if convention_pins:
        pin[SOURCE_MODEL_CONVENTION_PINS_FIELD] = convention_pins
    return pin, ""


def manifest_structure_payload(manifest: Mapping[str, Any]) -> dict[str, Any] | None:
    """Return the exact atom/ref/role structure independent of display/hash fields."""

    normalized = normalize_signature_manifest(dict(manifest))
    if normalized is None:
        return None
    atoms = normalized.get("atoms")
    if not isinstance(atoms, list):
        return None
    out_atoms: list[dict[str, Any]] = []
    for atom in atoms:
        if not isinstance(atom, Mapping):
            return None
        role = str(atom.get("role") or "").strip().lower()
        ref = str(atom.get("ref") or "").strip()
        canonical = atom.get("canonical")
        if not ref or role not in {"parameter", "assumption", "conclusion"} or canonical is None:
            return None
        projected: dict[str, Any] = {
            "ref": ref,
            "role": role,
            "canonical": canonical,
        }
        if role != "conclusion":
            binder = str(atom.get("binder_info") or "").strip()
            if not binder:
                return None
            projected["binder_info"] = binder
        out_atoms.append(projected)
    return {
        "schema": REUSE_SCHEMA,
        "declaration_kind": normalized.get("declaration_kind"),
        "conclusion_mode": normalized.get("conclusion_mode"),
        "atoms": out_atoms,
    }


def manifest_structure_sha256(manifest: Mapping[str, Any]) -> str:
    payload = manifest_structure_payload(manifest)
    return _stable_digest(payload) if payload is not None else ""


def semantic_dependency_sha256(
    manifest: Mapping[str, Any],
) -> tuple[str, str]:
    """Return the current name-independent transitive semantic identity.

    Lean owns dependency discovery from the elaborated proposition and
    reachable constant graph. The shared manifest generator also pins exact
    artifacts for opaque imported terminals whose bodies are not represented
    in that graph. Whole paper-module artifacts and theorem proof bodies are
    deliberately absent, so an unrelated edit or replacing ``sorry`` does not
    invalidate a statement judgment.
    """

    dependency = semantic_dependency_manifest(manifest)
    if not isinstance(dependency, Mapping) or dependency.get("complete") is not True:
        return "", "row has no complete transitive semantic dependency manifest"
    digest = _valid_digest(dependency.get("semantic_dependency_sha256"))
    if not digest:
        return "", "row semantic dependency manifest has no canonical digest"
    recorded = manifest.get("semantic_dependency_manifest")
    if not isinstance(recorded, Mapping):
        return "", "row does not retain its generated semantic dependency manifest"
    if _valid_digest(recorded.get("semantic_dependency_sha256")) != digest:
        return "", "row semantic dependency manifest is stale"
    if recorded.get("complete") is not True:
        return "", "row recorded semantic dependency manifest is incomplete"
    return digest, ""


def _manifest_atom_index(
    manifest: Mapping[str, Any], *, require_current_digest: bool
) -> tuple[dict[str, dict[str, Any]], str]:
    normalized = normalize_signature_manifest(dict(manifest))
    if normalized is None:
        return {}, "manifest is not a valid schema-2 elaborated signature"
    current_digest = signature_manifest_digest(normalized)
    if not current_digest:
        return {}, "manifest has no canonical digest"
    if require_current_digest and _valid_digest(manifest.get("sha256")) != current_digest:
        return {}, "current manifest sha256 is stale"
    atoms = normalized.get("atoms")
    if not isinstance(atoms, list):
        return {}, "manifest has no atom list"
    result: dict[str, dict[str, Any]] = {}
    for atom in atoms:
        if not isinstance(atom, dict):
            return {}, "manifest has a malformed atom"
        ref = str(atom.get("ref") or "").strip()
        if not ref or ref in result:
            return {}, "manifest has a missing or duplicate atom ref"
        result[ref] = atom
    return result, ""


def _legacy_ledger_atoms_match_manifest(
    entry: Mapping[str, Any], manifest: Mapping[str, Any]
) -> str:
    """Validate old atom refs/roles before a serializer-refresh migration."""

    atoms, error = _manifest_atom_index(manifest, require_current_digest=False)
    if error:
        return error
    obligations = entry.get("lean_obligations")
    if not isinstance(obligations, list) or not obligations:
        return "statement item has no Lean obligation ledger"
    seen: set[str] = set()
    for obligation in obligations:
        if not isinstance(obligation, Mapping):
            return "statement item has a malformed Lean obligation"
        ref = str(obligation.get("signature_ref") or "").strip()
        role = str(obligation.get("kind") or "").strip().lower()
        if not ref or ref in seen or ref not in atoms:
            return "statement item Lean obligations do not uniquely bind manifest atoms"
        atom = atoms[ref]
        if role != str(atom.get("role") or "").strip().lower():
            return "statement item Lean obligation role differs from prior manifest"
        expected = review_dashboard.signature_manifest_atom_digest(atom)
        if _valid_digest(obligation.get("signature_atom_sha256")) != expected:
            return "statement item Lean atom digest differs from prior manifest"
        seen.add(ref)
    if seen != set(atoms):
        return "statement item Lean obligations do not partition prior manifest atoms"
    return ""


def route_semantic_sha256(route: Mapping[str, Any]) -> str:
    """Hash route semantics while excluding source navigation coordinates."""

    return _stable_digest(
        {
            str(key): value
            for key, value in route.items()
            if str(key) not in ROUTE_NAVIGATION_FIELDS
        }
    )


def _route_matches_item(route: Mapping[str, Any], item: Mapping[str, Any]) -> str:
    statement, target_digest = review_dashboard._source_item_coverage_statement(dict(item))
    location = review_dashboard._source_item_coverage_location(dict(item))
    if not statement or not target_digest or not location:
        return "source item has incomplete canonical target/location"
    if _valid_digest(route.get("source_statement_sha256")) != target_digest:
        return "route source_statement_sha256 does not match its source item"
    if str(route.get("source_location") or "").strip() != location:
        return "route source_location does not match its source item"
    target = review_dashboard._source_item_corrected_target(dict(item))
    if target is None:
        return ""
    approval = target.get("approval")
    if not isinstance(approval, Mapping):
        return "corrected source item has no approval object"
    expected_archival = _valid_digest(item.get("statement_sha256"))
    expected_target = _valid_digest(target.get("corrected_target_sha256"))
    if str(route.get("route_kind") or "").strip().lower() != "approved_corrected_target":
        return "corrected source item route is not approved_corrected_target"
    if _valid_digest(route.get("archival_statement_sha256")) != expected_archival:
        return "corrected route archival statement pin is stale"
    if _valid_digest(route.get("corrected_target_sha256")) != expected_target:
        return "corrected route target pin is stale"
    if sorted(_string_list(route.get("governing_defect_ids"))) != sorted(
        _string_list(target.get("governing_defect_ids"))
    ):
        return "corrected route governing defect ids differ from the source target"
    if route.get("archival_equivalence_claimed") is not False:
        return "corrected route can not claim archival equivalence"
    if _valid_digest(route.get("approval_artifact_sha256")) != _valid_digest(
        approval.get("artifact_sha256")
    ):
        return "corrected route approval artifact pin is stale"
    return ""


def _rewrite_route_for_item(
    route: Mapping[str, Any], key: str, item: Mapping[str, Any]
) -> dict[str, Any]:
    copied = copy.deepcopy(dict(route))
    _statement, target_digest = review_dashboard._source_item_coverage_statement(dict(item))
    location = review_dashboard._source_item_coverage_location(dict(item))
    copied["source_item"] = key
    copied["source_statement_sha256"] = target_digest
    copied["source_location"] = location
    for field in (
        "source_component_anchor_sha256",
        "source_definition_partition_sha256",
        "source_definition_component_sha256",
    ):
        current = item.get(field)
        if current is None:
            copied.pop(field, None)
        else:
            copied[field] = current
    target = review_dashboard._source_item_corrected_target(dict(item))
    if target is not None:
        approval = target.get("approval")
        approval = approval if isinstance(approval, Mapping) else {}
        copied.update(
            {
                "archival_statement_sha256": _valid_digest(item.get("statement_sha256")),
                "archival_source_location": location,
                "corrected_target_sha256": _valid_digest(
                    target.get("corrected_target_sha256")
                ),
                "governing_defect_ids": _string_list(target.get("governing_defect_ids")),
                "archival_equivalence_claimed": False,
                "approval_artifact_sha256": _valid_digest(
                    approval.get("artifact_sha256")
                ),
            }
        )
    return copied


def _rewrite_source_obligations(
    entry: dict[str, Any], route_rebindings: list["RouteRebinding"]
) -> str:
    """Rewrite only exact source-item navigation embedded in obligation rows."""

    obligations = entry.get("source_obligations")
    if not isinstance(obligations, list):
        return "statement item has no source obligation ledger"
    by_old_key = {binding.old_key: binding for binding in route_rebindings}
    for obligation in obligations:
        if not isinstance(obligation, dict):
            return "statement item has a malformed source obligation"
        old_key = str(obligation.get("source_item") or "").strip()
        binding = by_old_key.get(old_key)
        if binding is None:
            continue
        if _valid_digest(obligation.get("source_statement_sha256")) != binding.old_target_sha256:
            return "source obligation does not retain the routed source target digest"
        if str(obligation.get("source_location") or "").strip() != binding.old_location:
            return "source obligation does not retain the routed source location"
        if review_dashboard.statement_digest(str(obligation.get("statement") or "")) != binding.old_target_sha256:
            return "source obligation text does not retain the routed source target"
        obligation["source_item"] = binding.current_key
        obligation["source_statement_sha256"] = binding.current_target_sha256
        obligation["source_location"] = binding.current_location
    return ""


@dataclass(frozen=True)
class RowSnapshot:
    name: str
    lean_statement: str
    paper_statement: str
    tex_statement: str
    manifest: dict[str, Any]
    declared_signature_sha256: str = ""

    @property
    def raw_lean_sha256(self) -> str:
        """Return an exact-byte digest, deliberately stricter than dashboard text.

        The existing sidecar field uses ``statement_digest`` for historical
        compatibility, which normalizes whitespace.  A reuse pin additionally
        records this exact string digest so a serializer/cache refresh cannot
        silently move a judgment to a different raw Lean declaration.
        """

        return _sha256_text(self.lean_statement)

    @property
    def normalized_lean_sha256(self) -> str:
        return review_dashboard.statement_digest(self.lean_statement)


@dataclass(frozen=True)
class RouteRebinding:
    old_key: str
    current_key: str
    old_target_sha256: str
    current_target_sha256: str
    old_location: str
    current_location: str
    old_route_semantic_sha256: str


@dataclass
class StatementBinding:
    old_signature_sha256: str
    current_row_name: str
    raw_lean_sha256: str
    manifest_structure_sha256: str
    semantic_dependency_sha256: str


@dataclass(frozen=True)
class SourcePinCache:
    """One immutable-by-convention source identity pass for a migration.

    Computing a source pin canonicalizes the complete item, its quoted source
    anchors, corrected-target disposition, and any governing model convention.
    A closeout can route the same item through statement and coverage ledgers,
    so recomputing that identity in every lane adds substantial JSON work but
    no independent evidence.  This cache is process-local and is rebuilt from
    the current inputs for every command.  Callers must copy a pin before
    adding route-local fields.
    """

    by_key: dict[str, dict[str, Any]]
    by_identity: dict[str, list[tuple[str, dict[str, Any]]]]
    errors: dict[str, str]


def row_snapshots_from_cache(payload: Mapping[str, Any]) -> list[RowSnapshot]:
    rows = payload.get("rows")
    if not isinstance(rows, list):
        return []
    snapshots: list[RowSnapshot] = []
    for raw in rows:
        if not isinstance(raw, Mapping):
            continue
        name = str(raw.get("name") or "").strip()
        lean = str(raw.get("lean_statement") or "")
        manifest = raw.get("lean_signature_manifest")
        if not name or not lean or not isinstance(manifest, dict):
            continue
        snapshots.append(
            RowSnapshot(
                name=name,
                lean_statement=lean,
                paper_statement=str(raw.get("paper_statement") or ""),
                tex_statement=str(raw.get("agent_statement") or ""),
                manifest=copy.deepcopy(manifest),
                declared_signature_sha256=str(
                    raw.get("lean_signature_sha256") or ""
                ).strip(),
            )
        )
    return snapshots


def row_snapshots_from_dashboard(rows: Iterable[Any]) -> list[RowSnapshot]:
    snapshots: list[RowSnapshot] = []
    for row in rows:
        name = str(getattr(row, "name", "") or "").strip()
        lean = str(getattr(row, "lean_statement", "") or "")
        manifest = getattr(row, "lean_signature_manifest", None)
        if not name or not lean or not isinstance(manifest, dict):
            continue
        snapshots.append(
            RowSnapshot(
                name=name,
                lean_statement=lean,
                paper_statement=str(getattr(row, "paper_statement", "") or ""),
                tex_statement=str(getattr(row, "agent_statement", "") or ""),
                manifest=copy.deepcopy(manifest),
                declared_signature_sha256=str(
                    getattr(row, "lean_signature_sha256", "") or ""
                ).strip(),
            )
        )
    return snapshots


def _verified_row_signature(row: RowSnapshot) -> tuple[str, str, str]:
    """Verify one row's current elaborated signature and structural identity.

    The legacy-v4 migration is deliberately stricter than ordinary cache
    discovery.  A cache snapshot is evidence only if the signature it records
    still hashes to the elaborated schema-2 manifest under the current
    canonical serializer.  Accepting an opaque historical hash would make the
    new v5 row pin an unaudited assertion.
    """

    normalized = normalize_signature_manifest(dict(row.manifest))
    if normalized is None:
        return "", "", "row has no valid elaborated schema-2 signature manifest"
    recorded = _valid_digest(row.manifest.get("sha256"))
    canonical = signature_manifest_digest(normalized)
    if not recorded or not canonical or recorded != canonical:
        return "", "", "row manifest sha256 is missing or stale"
    declared = _valid_digest(row.declared_signature_sha256)
    if not declared or declared != recorded:
        return "", "", "row declared Lean signature is missing or differs from its manifest"
    structure = manifest_structure_sha256(row.manifest)
    if not structure:
        return "", "", "row manifest has no structural identity"
    _dependency, dependency_error = semantic_dependency_sha256(row.manifest)
    if dependency_error:
        return "", "", dependency_error
    return recorded, structure, ""


def _legacy_v4_rows_from_review_cache(
    payload: Mapping[str, Any],
) -> tuple[dict[str, list[RowSnapshot]], dict[str, list[str]], str]:
    """Read a supplied pre-change cache with its explicit row-signature pins.

    Legacy coverage rows have only a row name, so the snapshot row name can
    locate a candidate but can never prove that it is the same row.  This
    loader checks the cache's own ``lean_signature_sha256`` against the
    manifest before later matching a name-independent elaborated manifest
    identity to one current row.
    """

    raw_rows = payload.get("rows")
    if not isinstance(raw_rows, list) or not raw_rows:
        return {}, {}, "previous review cache has no row list"
    by_name: dict[str, list[RowSnapshot]] = {}
    errors: dict[str, list[str]] = {}
    for raw in raw_rows:
        if not isinstance(raw, Mapping):
            continue
        name = str(raw.get("name") or "").strip()
        if not name:
            continue
        lean = str(raw.get("lean_statement") or "")
        manifest = raw.get("lean_signature_manifest")
        if not lean or not isinstance(manifest, dict):
            errors.setdefault(name, []).append(
                "previous review-cache row has no Lean statement or manifest"
            )
            continue
        declared_signature = _valid_digest(raw.get("lean_signature_sha256"))
        manifest_signature = _valid_digest(manifest.get("sha256"))
        if not declared_signature or declared_signature != manifest_signature:
            errors.setdefault(name, []).append(
                "previous review-cache row signature does not match its manifest"
            )
            continue
        row = RowSnapshot(
            name=name,
            lean_statement=lean,
            paper_statement=str(raw.get("paper_statement") or ""),
            tex_statement=str(raw.get("agent_statement") or ""),
            manifest=copy.deepcopy(manifest),
            declared_signature_sha256=declared_signature,
        )
        _signature, _structure, signature_error = _verified_row_signature(row)
        if signature_error:
            errors.setdefault(name, []).append(
                f"previous review-cache {signature_error}"
            )
            continue
        by_name.setdefault(name, []).append(row)
    if not by_name:
        details = "; ".join(
            f"{name}: {message}"
            for name, messages in sorted(errors.items())
            for message in messages
        )
        return (
            {},
            errors,
            "previous review cache has no usable signed rows"
            + (f": {details}" if details else ""),
        )
    return by_name, errors, ""


def _row_locator_identity(
    *,
    manifest_structure_sha256: str,
    semantic_dependency_sha256: str,
    paper_statement_sha256: str,
) -> str:
    """Compose the name-free identity used only to locate one review row."""

    if not all(
        _valid_digest(digest)
        for digest in (
            manifest_structure_sha256,
            semantic_dependency_sha256,
            paper_statement_sha256,
        )
    ):
        return ""
    return _stable_digest(
        {
            "manifest_structure_sha256": manifest_structure_sha256,
            "semantic_dependency_sha256": semantic_dependency_sha256,
            "paper_statement_sha256": paper_statement_sha256,
        }
    )


def _manifest_structure_row_identity(row: RowSnapshot) -> tuple[str, str, str]:
    """Return a declaration-name-independent row locator from its manifest.

    The pretty-printed Lean declaration starts with the declaration name, so
    matching that raw string would make a harmless function rename block a
    semantic reuse.  The elaborated manifest structure carries every binder,
    role, and canonical type/value atom without using that navigation name.
    The paper-facing text is retained as a separate human-review boundary.

    This deliberately does not certify the signature hash.  The caller uses
    it to locate a candidate and then invokes ``_verified_row_signature`` so a
    stale current signature gets a specific fail-closed diagnostic instead of
    disappearing from the candidate index.
    """

    structure = manifest_structure_sha256(row.manifest)
    if not structure:
        return "", "", "row manifest has no structural identity"
    dependency, dependency_error = semantic_dependency_sha256(row.manifest)
    if dependency_error:
        return "", "", dependency_error
    if not row.paper_statement:
        return "", "", "row has no paper-facing statement text"
    paper_digest = review_dashboard.statement_digest(row.paper_statement)
    identity = _row_locator_identity(
        manifest_structure_sha256=structure,
        semantic_dependency_sha256=dependency,
        paper_statement_sha256=paper_digest,
    )
    if not identity:
        return "", "", "row has no canonical semantic locator identity"
    return identity, structure, ""


def _semantic_row_identity(row: RowSnapshot) -> tuple[str, str, str, str]:
    """Return a fully verified declaration-name-independent row identity."""

    signature, structure, signature_error = _verified_row_signature(row)
    if signature_error:
        return "", "", "", signature_error
    identity, identity_structure, identity_error = _manifest_structure_row_identity(row)
    if identity_error:
        return "", "", "", identity_error
    if structure != identity_structure:
        return "", "", "", "row manifest structural identity changed during verification"
    return identity, signature, structure, ""


def _unique_by_semantic_row_identity(
    rows: Iterable[RowSnapshot],
) -> dict[str, list[RowSnapshot]]:
    """Index candidate rows by a declaration-name-independent structure."""

    out: dict[str, list[RowSnapshot]] = {}
    for row in rows:
        identity, _structure, error = _manifest_structure_row_identity(row)
        if error:
            continue
        out.setdefault(identity, []).append(row)
    return out


def _unique_by_raw_lean(rows: Iterable[RowSnapshot]) -> dict[str, list[RowSnapshot]]:
    out: dict[str, list[RowSnapshot]] = {}
    for row in rows:
        out.setdefault(row.normalized_lean_sha256, []).append(row)
    return out


def _rows_by_paper_statement(
    rows: Iterable[RowSnapshot],
) -> dict[str, list[RowSnapshot]]:
    """Index rows by reviewed paper text before checking elaborated pins."""

    out: dict[str, list[RowSnapshot]] = {}
    for row in rows:
        if not row.paper_statement:
            continue
        digest = review_dashboard.statement_digest(row.paper_statement)
        if digest:
            out.setdefault(digest, []).append(row)
    return out


def _source_pin_cache(
    inventory: Mapping[str, Mapping[str, Any]],
    mode: str,
    *,
    source_proof_fidelity: Mapping[str, Any] | None = None,
) -> SourcePinCache:
    """Compute each current source identity once, independent of map keys."""

    index: dict[str, list[tuple[str, dict[str, Any]]]] = {}
    pins: dict[str, dict[str, Any]] = {}
    errors: dict[str, str] = {}
    for key, raw_item in inventory.items():
        key = str(key)
        item = dict(raw_item)
        pin, error = source_reuse_pin(
            item, mode, source_proof_fidelity=source_proof_fidelity
        )
        if pin is None:
            errors[key] = error
            continue
        identity = _stable_digest(pin)
        pins[key] = pin
        index.setdefault(identity, []).append((key, item))
    return SourcePinCache(by_key=pins, by_identity=index, errors=errors)


def _project_source_pin_cache(
    base: SourcePinCache,
    keys: set[str],
) -> SourcePinCache:
    """Project a cache to selected keys without recomputing source identities."""

    pins = {key: pin for key, pin in base.by_key.items() if key in keys}
    errors = {key: error for key, error in base.errors.items() if key in keys}
    index: dict[str, list[tuple[str, dict[str, Any]]]] = {}
    for identity, candidates in base.by_identity.items():
        selected = [(key, item) for key, item in candidates if key in keys]
        if selected:
            index[identity] = selected
    return SourcePinCache(by_key=pins, by_identity=index, errors=errors)


def _source_pin_index(
    inventory: Mapping[str, Mapping[str, Any]],
    mode: str,
    *,
    source_proof_fidelity: Mapping[str, Any] | None = None,
) -> tuple[dict[str, list[tuple[str, dict[str, Any]]]], dict[str, str]]:
    """Compatibility wrapper returning the content index and item errors."""

    cache = _source_pin_cache(
        inventory,
        mode,
        source_proof_fidelity=source_proof_fidelity,
    )
    return cache.by_identity, cache.errors


def _reuse_pin_from_embedded(
    entry: Mapping[str, Any],
    routes: list[Mapping[str, Any]],
    *,
    current_validator_identity_sha256: str = "",
) -> tuple[dict[str, Any] | None, str]:
    raw = entry.get(REUSE_FIELD)
    if not isinstance(raw, Mapping) or raw.get("schema") != ENTRY_REUSE_SCHEMA:
        return None, "no entry-local semantic reuse pin"
    if not formalization_protocol_receipt_matches(raw, scope="review"):
        return None, "entry-local formalization protocol pin is missing or stale"
    if current_validator_identity_sha256:
        recorded_validator = _valid_digest(
            raw.get("review_validator_identity_sha256")
        )
        if recorded_validator != current_validator_identity_sha256:
            return None, "entry-local review validator identity is missing or stale"
    raw_digest = _valid_digest(raw.get("raw_lean_statement_sha256"))
    normalized_digest = _valid_digest(raw.get("normalized_lean_statement_sha256"))
    if not raw_digest or not normalized_digest or normalized_digest != _valid_digest(
        entry.get("lean_statement_sha256")
    ):
        return None, "entry-local raw Lean statement pin is missing or stale"
    structure = _valid_digest(raw.get("manifest_structure_sha256"))
    if not structure:
        return None, "entry-local manifest structure pin is missing"
    dependency = _valid_digest(raw.get("semantic_dependency_sha256"))
    if not dependency:
        return None, "entry-local transitive semantic dependency pin is missing"
    paper_digest = _valid_digest(raw.get("paper_statement_sha256"))
    tex_digest = _valid_digest(raw.get("tex_statement_sha256"))
    if (
        not paper_digest
        or paper_digest != _valid_digest(entry.get("paper_statement_sha256"))
    ):
        return None, "entry-local paper statement pin is missing or stale"
    if (
        not tex_digest
        or tex_digest != _valid_digest(entry.get("tex_statement_sha256"))
    ):
        return None, "entry-local Lean-to-TeX statement pin is missing or stale"
    stored_routes = raw.get("source_routes")
    if not isinstance(stored_routes, list) or len(stored_routes) != len(routes):
        return None, "entry-local source route pins are missing or stale"
    stored_by_route: dict[str, list[dict[str, Any]]] = {}
    for pin in stored_routes:
        if not isinstance(pin, dict):
            return None, "entry-local source route pin is malformed"
        digest = _valid_digest(pin.get("route_semantic_sha256"))
        if not digest:
            return None, "entry-local source route semantic pin is missing"
        stored_by_route.setdefault(digest, []).append(pin)
    pins: list[dict[str, Any]] = []
    for route in routes:
        digest = route_semantic_sha256(route)
        candidates = stored_by_route.get(digest, [])
        if len(candidates) != 1:
            return None, "entry-local source route semantic identity is ambiguous or stale"
        pins.append(copy.deepcopy(candidates[0]))
    return {
        "raw_lean_statement_sha256": raw_digest,
        "normalized_lean_statement_sha256": normalized_digest,
        "manifest_structure_sha256": structure,
        "semantic_dependency_sha256": dependency,
        "paper_statement_sha256": paper_digest,
        "tex_statement_sha256": tex_digest,
        "source_routes": pins,
    }, ""


def _reuse_pin_from_legacy(
    entry: Mapping[str, Any],
    routes: Sequence[Mapping[str, Any]],
    *,
    previous_inventory: Mapping[str, Mapping[str, Any]] | None,
    previous_mode: str,
    previous_rows_by_raw: Mapping[str, list[RowSnapshot]] | None,
    previous_source_proof_fidelity: Mapping[str, Any] | None = None,
) -> tuple[dict[str, Any] | None, str]:
    if previous_inventory is None or previous_rows_by_raw is None or not previous_mode:
        return (
            None,
            "no entry-local semantic reuse pin; provide both previous source map and review cache",
        )
    raw_digest = _valid_digest(entry.get("lean_statement_sha256"))
    if not raw_digest:
        return None, "statement item has no raw Lean statement digest"
    rows = previous_rows_by_raw.get(raw_digest, [])
    if len(rows) != 1:
        return None, "prior raw Lean statement does not identify exactly one prior review row"
    old_row = rows[0]
    if old_row.normalized_lean_sha256 != raw_digest:
        return None, "prior raw Lean statement does not match the sidecar digest"
    old_signature = _valid_digest(old_row.manifest.get("sha256"))
    if not old_signature or old_signature != _valid_digest(entry.get("lean_signature_sha256")):
        return None, "statement item signature is not bound to its prior manifest"
    structure = manifest_structure_sha256(old_row.manifest)
    if not structure:
        return None, "prior manifest has no structural identity"
    dependency, dependency_error = semantic_dependency_sha256(old_row.manifest)
    if dependency_error:
        return None, f"prior {dependency_error}"
    paper_digest = _valid_digest(entry.get("paper_statement_sha256"))
    tex_digest = _valid_digest(entry.get("tex_statement_sha256"))
    if not paper_digest or paper_digest != review_dashboard.statement_digest(
        old_row.paper_statement
    ):
        return None, "prior paper statement pin is missing or stale"
    if not tex_digest or tex_digest != review_dashboard.statement_digest(
        old_row.tex_statement
    ):
        return None, "prior Lean-to-TeX statement pin is missing or stale"
    atom_error = _legacy_ledger_atoms_match_manifest(entry, old_row.manifest)
    if atom_error:
        return None, atom_error
    pins: list[dict[str, Any]] = []
    for route in routes:
        old_key = str(route.get("source_item") or "").strip()
        old_item = previous_inventory.get(old_key)
        if old_item is None:
            return None, "prior source route does not identify a prior source item"
        route_error = _route_matches_item(route, old_item)
        if route_error:
            return None, route_error
        source_pin, source_error = source_reuse_pin(
            old_item,
            previous_mode,
            source_proof_fidelity=previous_source_proof_fidelity,
        )
        if source_pin is None:
            return None, source_error
        source_pin["route_semantic_sha256"] = route_semantic_sha256(route)
        pins.append(source_pin)
    return {
        "raw_lean_statement_sha256": old_row.raw_lean_sha256,
        "normalized_lean_statement_sha256": raw_digest,
        "manifest_structure_sha256": structure,
        "semantic_dependency_sha256": dependency,
        "paper_statement_sha256": paper_digest,
        "tex_statement_sha256": tex_digest,
        "source_routes": pins,
    }, ""


def _source_route_rebindings(
    routes: list[Mapping[str, Any]],
    pins: list[Mapping[str, Any]],
    *,
    current_index: Mapping[str, list[tuple[str, dict[str, Any]]]],
    current_anchor_errors: Mapping[str, list[str]] | None,
) -> tuple[list[RouteRebinding] | None, list[dict[str, Any]] | None, str]:
    if current_anchor_errors is None:
        return None, None, "current byte-anchor validation was not supplied"
    if len(routes) != len(pins):
        return None, None, "source route count differs from its semantic reuse pins"
    rebinding: list[RouteRebinding] = []
    rewritten: list[dict[str, Any]] = []
    used_current_keys: set[str] = set()
    for route, pin in zip(routes, pins, strict=True):
        expected_route_digest = _valid_digest(pin.get("route_semantic_sha256"))
        if not expected_route_digest or expected_route_digest != route_semantic_sha256(route):
            return None, None, "source route semantic/convention pin changed"
        source_pin = {
            key: pin.get(key)
            for key in (
                "schema",
                "source_item_semantic_sha256",
                "source_anchor_quote_identity_sha256",
                "source_target_sha256",
                "source_target_disposition",
            )
        }
        # Legacy ordinary pins predate convention records.  Preserve absence,
        # rather than serializing it as a new null field, so those independently
        # unchanged source items retain their exact identity.
        if SOURCE_MODEL_CONVENTION_PINS_FIELD in pin:
            source_pin[SOURCE_MODEL_CONVENTION_PINS_FIELD] = pin.get(
                SOURCE_MODEL_CONVENTION_PINS_FIELD
            )
        identity = _stable_digest(source_pin)
        candidates = current_index.get(identity, [])
        if len(candidates) != 1:
            return None, None, "source semantic/quote identity is missing or ambiguous in current map"
        current_key, current_item = candidates[0]
        if current_key in used_current_keys:
            return None, None, "two old routes map to one current source item"
        if current_anchor_errors.get(current_key):
            return None, None, "current source anchor is not byte-verified"
        old_key = str(route.get("source_item") or "").strip()
        old_target = _valid_digest(route.get("source_statement_sha256"))
        old_location = str(route.get("source_location") or "").strip()
        current_statement, current_target = review_dashboard._source_item_coverage_statement(
            current_item
        )
        current_location = review_dashboard._source_item_coverage_location(current_item)
        if not old_key or not old_target or not old_location or not current_statement or not current_target or not current_location:
            return None, None, "source route has incomplete source navigation pins"
        rewritten_route = _rewrite_route_for_item(route, current_key, current_item)
        # All semantic/corrected-target/convention fields must be invariant.
        if route_semantic_sha256(rewritten_route) != expected_route_digest:
            return None, None, "source corrected-target or convention pin changed"
        rebinding.append(
            RouteRebinding(
                old_key=old_key,
                current_key=current_key,
                old_target_sha256=old_target,
                current_target_sha256=current_target,
                old_location=old_location,
                current_location=current_location,
                old_route_semantic_sha256=expected_route_digest,
            )
        )
        rewritten.append(rewritten_route)
        used_current_keys.add(current_key)
    return rebinding, rewritten, ""


def _rewrite_lean_atom_digests(entry: dict[str, Any], manifest: Mapping[str, Any]) -> str:
    atoms, error = _manifest_atom_index(manifest, require_current_digest=True)
    if error:
        return error
    obligations = entry.get("lean_obligations")
    if not isinstance(obligations, list):
        return "statement item has no Lean obligations"
    seen: set[str] = set()
    for obligation in obligations:
        if not isinstance(obligation, dict):
            return "statement item has a malformed Lean obligation"
        ref = str(obligation.get("signature_ref") or "").strip()
        if not ref or ref in seen or ref not in atoms:
            return "statement item Lean obligation refs are not a manifest partition"
        atom = atoms[ref]
        if str(obligation.get("kind") or "").strip().lower() != str(
            atom.get("role") or ""
        ).strip().lower():
            return "statement item Lean obligation role differs from current manifest"
        obligation["signature_atom_sha256"] = review_dashboard.signature_manifest_atom_digest(atom)
        seen.add(ref)
    if seen != set(atoms):
        return "statement item Lean obligations do not cover current manifest atoms"
    current_signature = _valid_digest(manifest.get("sha256"))
    if not current_signature:
        return "current manifest has no canonical sha256"
    entry["lean_signature_sha256"] = current_signature
    return ""


def _entry_reuse_metadata(
    *,
    row: RowSnapshot,
    routes: Sequence[Mapping[str, Any]],
    inventory: Mapping[str, Mapping[str, Any]],
    mode: str,
    paper_statement_sha256: str = "",
    source_proof_fidelity: Mapping[str, Any] | None = None,
    source_pin_cache: SourcePinCache | None = None,
    validator_identity_sha256: str = "",
) -> tuple[dict[str, Any] | None, str]:
    structure = manifest_structure_sha256(row.manifest)
    if not structure:
        return None, "current manifest has no structural identity"
    dependency, dependency_error = semantic_dependency_sha256(row.manifest)
    if dependency_error:
        return None, dependency_error
    route_pins: list[dict[str, Any]] = []
    for route in routes:
        key = str(route.get("source_item") or "").strip()
        item = inventory.get(key)
        if item is None:
            return None, "rewritten route does not identify a current source item"
        cached_pin = source_pin_cache.by_key.get(key) if source_pin_cache else None
        if cached_pin is not None:
            pin = copy.deepcopy(cached_pin)
        else:
            pin, error = source_reuse_pin(
                item, mode, source_proof_fidelity=source_proof_fidelity
            )
            if pin is None:
                if source_pin_cache is not None:
                    error = source_pin_cache.errors.get(key, error)
                return None, error
        pin["route_semantic_sha256"] = route_semantic_sha256(route)
        route_pins.append(pin)
    paper_digest = _valid_digest(paper_statement_sha256)
    if paper_statement_sha256 and not paper_digest:
        return None, "entry-local paper statement digest is malformed"
    if not paper_digest:
        paper_digest = review_dashboard.statement_digest(row.paper_statement)
    metadata = {
        "schema": ENTRY_REUSE_SCHEMA,
        FORMALIZATION_REVIEW_PROTOCOL_FIELD: (
            formalization_review_protocol_digest()
        ),
        "raw_lean_statement_sha256": row.raw_lean_sha256,
        "normalized_lean_statement_sha256": row.normalized_lean_sha256,
        "paper_statement_sha256": paper_digest,
        "tex_statement_sha256": review_dashboard.statement_digest(row.tex_statement),
        "manifest_structure_sha256": structure,
        "semantic_dependency_sha256": dependency,
        "source_routes": route_pins,
    }
    if validator_identity_sha256:
        if not _valid_digest(validator_identity_sha256):
            return None, "current review validator identity is malformed"
        metadata["review_validator_identity_sha256"] = validator_identity_sha256
    return metadata, ""


def _bootstrap_current_statement_entry(
    entry: dict[str, Any],
    row: RowSnapshot,
    routes: Sequence[Mapping[str, Any]],
    *,
    current_inventory: Mapping[str, Mapping[str, Any]],
    current_mode: str,
    current_anchor_errors: Mapping[str, list[str]] | None,
    current_source_proof_fidelity: Mapping[str, Any] | None,
    current_source_pin_cache: SourcePinCache | None,
    validator_identity_sha256: str,
    validate_entry: Callable[[dict[str, Any], RowSnapshot, Mapping[str, Mapping[str, Any]]], str]
    | None,
) -> tuple[dict[str, Any] | None, str]:
    """Create reusable pins only for a fully current independently valid row."""

    if validate_entry is None:
        return None, "bootstrap requires a current full statement validator"
    if _valid_digest(entry.get("lean_signature_sha256")) != _valid_digest(
        row.manifest.get("sha256")
    ):
        return None, "bootstrap statement signature is not current"
    if current_anchor_errors is None:
        return None, "bootstrap requires current byte-anchor validation"
    for route in routes:
        key = str(route.get("source_item") or "").strip()
        item = current_inventory.get(key)
        if item is None:
            return None, "bootstrap route does not identify a current source item"
        if current_anchor_errors.get(key):
            return None, "bootstrap source anchor is not byte-verified"
        route_error = _route_matches_item(route, item)
        if route_error:
            return None, route_error
        source_pin = (
            current_source_pin_cache.by_key.get(key)
            if current_source_pin_cache is not None
            else None
        )
        source_pin_error = (
            current_source_pin_cache.errors.get(key, "")
            if current_source_pin_cache is not None
            else ""
        )
        if source_pin is None and current_source_pin_cache is None:
            source_pin, source_pin_error = source_reuse_pin(
                item,
                current_mode,
                source_proof_fidelity=current_source_proof_fidelity,
            )
        if source_pin is None:
            return None, f"bootstrap route has no current semantic source pin: {source_pin_error}"
    validation_error = validate_entry(entry, row, current_inventory)
    if validation_error:
        return None, validation_error
    component_routed = any(
        str(route.get("route_kind") or "").strip().lower() == "source_component"
        for route in routes
    )
    paper_statement_sha256 = (
        str(entry.get("paper_statement_sha256") or "").strip()
        if component_routed
        else ""
    )
    if component_routed and not _valid_digest(paper_statement_sha256):
        return None, "component-routed entry has no valid local paper statement digest"
    return _entry_reuse_metadata(
        row=row,
        routes=routes,
        inventory=current_inventory,
        mode=current_mode,
        paper_statement_sha256=paper_statement_sha256,
        source_proof_fidelity=current_source_proof_fidelity,
        source_pin_cache=current_source_pin_cache,
        validator_identity_sha256=validator_identity_sha256,
    )


def migrate_statement_items(
    statement_items: Mapping[str, Any],
    *,
    current_rows: Iterable[RowSnapshot],
    current_inventory: Mapping[str, Mapping[str, Any]],
    current_mode: str,
    current_anchor_errors: Mapping[str, list[str]] | None,
    current_source_proof_fidelity: Mapping[str, Any] | None = None,
    previous_inventory: Mapping[str, Mapping[str, Any]] | None = None,
    previous_mode: str = "",
    previous_rows: Iterable[RowSnapshot] | None = None,
    previous_source_proof_fidelity: Mapping[str, Any] | None = None,
    current_source_pin_cache: SourcePinCache | None = None,
    validator_identities: Mapping[str, str] | None = None,
    bootstrap_current: bool = False,
    validate_entry: Callable[[dict[str, Any], RowSnapshot, Mapping[str, Mapping[str, Any]]], str]
    | None = None,
) -> tuple[dict[str, Any], dict[str, dict[str, Any]], dict[str, StatementBinding]]:
    """Migrate individually provable statement judgments.

    The returned item object preserves rejected entries verbatim.  Decisions are
    keyed by the old sidecar key only for reporting; acceptance is based on the
    content identities above.
    """

    output = copy.deepcopy(dict(statement_items))
    decisions: dict[str, dict[str, Any]] = {}
    bindings: dict[str, StatementBinding] = {}
    current_rows = list(current_rows)
    current_by_raw = _unique_by_raw_lean(current_rows)
    current_by_paper_statement = _rows_by_paper_statement(current_rows)
    current_by_name: dict[str, list[RowSnapshot]] = {}
    for current_row in current_rows:
        current_by_name.setdefault(current_row.name, []).append(current_row)
    previous_by_raw = _unique_by_raw_lean(previous_rows or [])
    current_source_pin_cache = current_source_pin_cache or _source_pin_cache(
        current_inventory,
        current_mode,
        source_proof_fidelity=current_source_proof_fidelity,
    )
    current_source_index = current_source_pin_cache.by_identity

    for raw_name, raw_entry in statement_items.items():
        name = str(raw_name).strip()
        if not name or not isinstance(raw_entry, Mapping):
            continue
        entry = copy.deepcopy(dict(raw_entry))
        validator_identity = (
            _valid_digest(validator_identities.get(name))
            if validator_identities is not None
            else ""
        )
        if validator_identities is not None and not validator_identity:
            decisions[name] = {
                "accepted": False,
                "reason": "current review validator identity is missing or malformed",
            }
            continue
        routes = entry.get("source_routes")
        if not isinstance(routes, list) or not routes or not all(
            isinstance(route, Mapping) for route in routes
        ):
            decisions[name] = {"accepted": False, "reason": "statement item has no complete source routes"}
            continue
        pin, pin_error = _reuse_pin_from_embedded(
            entry,
            routes,
            current_validator_identity_sha256=validator_identity,
        )
        if pin is None and REUSE_FIELD not in entry:
            pin, pin_error = _reuse_pin_from_legacy(
                entry,
                routes,
                previous_inventory=previous_inventory,
                previous_mode=previous_mode,
                previous_rows_by_raw=previous_by_raw,
                previous_source_proof_fidelity=previous_source_proof_fidelity,
            )
        row: RowSnapshot | None = None
        component_routed = any(
            str(route.get("route_kind") or "").strip().lower()
            == "source_component"
            for route in routes
        )
        component_target_sha256 = ""
        if pin is not None:
            if component_routed:
                component_target_sha256 = (
                    review_dashboard._validated_unique_source_component_target_sha256(
                        {
                            "source_routes": routes,
                            "paper_statement_sha256": entry.get(
                                "paper_statement_sha256"
                            ),
                            # The embedded route-semantic pins were authenticated
                            # above; current source bytes are authenticated by the
                            # generic rebinding pass below.
                            "source_route_error": "",
                            "source_route_validation_performed": True,
                        }
                    )
                )
            if component_target_sha256:
                pinned_component_routes = [
                    route_pin
                    for route, route_pin in zip(routes, pin["source_routes"])
                    if str(route.get("route_kind") or "").strip().lower()
                    == "source_component"
                    and _valid_digest(route_pin.get("source_target_sha256"))
                    == component_target_sha256
                ]
                if (
                    component_target_sha256
                    != str(pin.get("paper_statement_sha256") or "")
                    or len(pinned_component_routes) != 1
                ):
                    decisions[name] = {
                        "accepted": False,
                        "reason": (
                            "entry-local component statement does not match one "
                            "authenticated source-component route"
                        ),
                    }
                    continue
                # The aggregate dashboard parent is display context, not the
                # reviewed component identity.  Re-identify the current row by
                # its entry-local Lean pin before checking manifest structure,
                # dependencies, and the component translation below.
                # The declaration's raw spelling includes its name. Locate
                # component rows by translated semantics first, then require
                # one exact manifest structure/dependency below. A rename can
                # therefore refresh navigation, while equal semantic
                # candidates remain deliberately ambiguous.
                paper_candidates = list(current_rows)
            else:
                exact_navigation = current_by_name.get(name, [])
                if exact_navigation:
                    paper_candidates = [
                        candidate
                        for candidate in exact_navigation
                        if len(exact_navigation) == 1
                        if review_dashboard.statement_digest(candidate.paper_statement)
                        == str(pin.get("paper_statement_sha256") or "")
                    ]
                else:
                    paper_candidates = current_by_paper_statement.get(
                        str(pin.get("paper_statement_sha256") or ""), []
                    )
            tex_candidates = [
                candidate
                for candidate in paper_candidates
                if review_dashboard.statement_digest(candidate.tex_statement)
                == pin["tex_statement_sha256"]
            ]
            if not tex_candidates:
                decisions[name] = {
                    "accepted": False,
                    "reason": "pinned Lean-to-TeX row identity is missing in current review surface",
                }
                continue
            structure_candidates = [
                candidate
                for candidate in tex_candidates
                if manifest_structure_sha256(candidate.manifest)
                == pin["manifest_structure_sha256"]
            ]
            if not structure_candidates:
                decisions[name] = {
                    "accepted": False,
                    "reason": (
                        "elaborated manifest atom/ref/role structure changed"
                        if len(tex_candidates) == 1
                        else "pinned paper/Lean row identity is missing or ambiguous"
                    ),
                }
                continue
            dependency_candidates: list[RowSnapshot] = []
            dependency_errors: list[str] = []
            for candidate in structure_candidates:
                candidate_dependency, candidate_error = semantic_dependency_sha256(
                    candidate.manifest
                )
                if candidate_error:
                    dependency_errors.append(candidate_error)
                elif candidate_dependency == pin["semantic_dependency_sha256"]:
                    dependency_candidates.append(candidate)
            if dependency_errors and len(structure_candidates) > 1:
                decisions[name] = {
                    "accepted": False,
                    "reason": (
                        "pinned semantic Lean row identity is unresolved or "
                        "ambiguous in current review surface"
                    ),
                }
                continue
            if len(dependency_candidates) == 1:
                row = dependency_candidates[0]
            elif not dependency_candidates and len(structure_candidates) == 1:
                decisions[name] = {
                    "accepted": False,
                    "reason": (
                        dependency_errors[0]
                        if dependency_errors
                        else (
                            "transitive elaborated semantic dependency or opaque "
                            "imported-terminal artifact changed"
                        )
                    ),
                }
                continue
            else:
                decisions[name] = {
                    "accepted": False,
                    "reason": (
                        "pinned semantic Lean row identity is missing or ambiguous "
                        "in current review surface"
                    ),
                }
                continue
        elif bootstrap_current:
            # Bootstrap does not reuse an earlier judgment. Locate the exact
            # current row first, then run the full validator before adding a
            # semantic pin.
            raw_digest = _valid_digest(entry.get("lean_statement_sha256"))
            exact_navigation = current_by_name.get(name, [])
            if exact_navigation:
                candidates = [
                    candidate
                    for candidate in exact_navigation
                    if len(exact_navigation) == 1
                    if candidate.normalized_lean_sha256 == raw_digest
                ]
            else:
                candidates = current_by_raw.get(raw_digest, [])
            if len(candidates) != 1:
                decisions[name] = {
                    "accepted": False,
                    "reason": (
                        "bootstrap raw Lean statement identity is missing or "
                        "ambiguous in current review surface"
                    ),
                }
                continue
            row = candidates[0]
        if pin is None:
            if not bootstrap_current:
                decisions[name] = {"accepted": False, "reason": pin_error}
                continue
            assert row is not None
            rewritten_routes: list[dict[str, Any]] = []
            for route in routes:
                key = str(route.get("source_item") or "").strip()
                item = current_inventory.get(key)
                if item is None:
                    decisions[name] = {
                        "accepted": False,
                        "reason": (
                            "bootstrap route does not identify a current source item"
                        ),
                    }
                    break
                rewritten_routes.append(_rewrite_route_for_item(route, key, item))
            if len(rewritten_routes) != len(routes):
                continue
            entry["source_routes"] = rewritten_routes
            metadata, bootstrap_error = _bootstrap_current_statement_entry(
                entry,
                row,
                rewritten_routes,
                current_inventory=current_inventory,
                current_mode=current_mode,
                current_anchor_errors=current_anchor_errors,
                current_source_proof_fidelity=current_source_proof_fidelity,
                current_source_pin_cache=current_source_pin_cache,
                validator_identity_sha256=validator_identity,
                validate_entry=validate_entry,
            )
            if metadata is None:
                decisions[name] = {"accepted": False, "reason": bootstrap_error}
                continue
            entry[REUSE_FIELD] = metadata
            output[name] = entry
            bindings[name] = StatementBinding(
                old_signature_sha256=_valid_digest(raw_entry.get("lean_signature_sha256")),
                current_row_name=row.name,
                raw_lean_sha256=row.raw_lean_sha256,
                manifest_structure_sha256=manifest_structure_sha256(row.manifest),
                semantic_dependency_sha256=str(
                    metadata["semantic_dependency_sha256"]
                ),
            )
            decisions[name] = {
                "accepted": True,
                "current_row": row.name,
                "bootstrap_current": True,
            }
            continue
        assert row is not None
        expected_paper_statement_sha256 = (
            component_target_sha256
            if component_target_sha256
            else review_dashboard.statement_digest(row.paper_statement)
        )
        if _valid_digest(entry.get("paper_statement_sha256")) != expected_paper_statement_sha256:
            decisions[name] = {"accepted": False, "reason": "paper statement digest changed"}
            continue
        if _valid_digest(entry.get("tex_statement_sha256")) != review_dashboard.statement_digest(
            row.tex_statement
        ):
            decisions[name] = {"accepted": False, "reason": "Lean-to-TeX statement digest changed"}
            continue
        current_structure = manifest_structure_sha256(row.manifest)
        if not current_structure or current_structure != pin["manifest_structure_sha256"]:
            decisions[name] = {
                "accepted": False,
                "reason": "elaborated manifest atom/ref/role structure changed",
            }
            continue
        current_dependency, dependency_error = semantic_dependency_sha256(
            row.manifest
        )
        if dependency_error:
            decisions[name] = {"accepted": False, "reason": dependency_error}
            continue
        if current_dependency != pin["semantic_dependency_sha256"]:
            decisions[name] = {
                "accepted": False,
                "reason": (
                    "transitive elaborated semantic dependency or opaque "
                    "imported-terminal artifact changed"
                ),
            }
            continue

        rebindings, rewritten_routes, route_error = _source_route_rebindings(
            [dict(route) for route in routes],
            [dict(route_pin) for route_pin in pin["source_routes"]],
            current_index=current_source_index,
            current_anchor_errors=current_anchor_errors,
        )
        if rebindings is None or rewritten_routes is None:
            decisions[name] = {"accepted": False, "reason": route_error}
            continue
        entry["source_routes"] = rewritten_routes
        source_error = _rewrite_source_obligations(entry, rebindings)
        if source_error:
            decisions[name] = {"accepted": False, "reason": source_error}
            continue
        atom_error = _rewrite_lean_atom_digests(entry, row.manifest)
        if atom_error:
            decisions[name] = {"accepted": False, "reason": atom_error}
            continue
        # Raw spelling is retained for traceability, but a declaration rename
        # or equivalent pretty-printer change is not a semantic identity. The
        # unique elaborated match above must succeed before this navigation pin
        # can be refreshed.
        entry["lean_statement_sha256"] = row.normalized_lean_sha256
        metadata, metadata_error = _entry_reuse_metadata(
            row=row,
            routes=rewritten_routes,
            inventory=current_inventory,
            mode=current_mode,
            paper_statement_sha256=component_target_sha256,
            source_proof_fidelity=current_source_proof_fidelity,
            source_pin_cache=current_source_pin_cache,
            validator_identity_sha256=validator_identity,
        )
        if metadata is None:
            decisions[name] = {"accepted": False, "reason": metadata_error}
            continue
        entry[REUSE_FIELD] = metadata
        if validate_entry is not None:
            validation_error = validate_entry(entry, row, current_inventory)
            if validation_error:
                decisions[name] = {"accepted": False, "reason": validation_error}
                continue
        output[name] = entry
        binding = StatementBinding(
            old_signature_sha256=_valid_digest(raw_entry.get("lean_signature_sha256")),
            current_row_name=row.name,
            raw_lean_sha256=row.raw_lean_sha256,
            manifest_structure_sha256=current_structure,
            semantic_dependency_sha256=current_dependency,
        )
        bindings[name] = binding
        decisions[name] = {
            "accepted": True,
            "current_row": row.name,
            "source_rebindings": [
                f"{binding.old_key} -> {binding.current_key}" for binding in rebindings
            ],
        }
    return output, decisions, bindings


def _coverage_source_pin_from_embedded(
    entry: Mapping[str, Any], *, current_validator_identity_sha256: str = ""
) -> tuple[dict[str, Any] | None, str]:
    raw = entry.get(REUSE_FIELD)
    if not isinstance(raw, Mapping) or raw.get("schema") != ENTRY_REUSE_SCHEMA:
        return None, "no entry-local semantic reuse pin"
    if not formalization_protocol_receipt_matches(raw, scope="review"):
        return None, "entry-local formalization protocol pin is missing or stale"
    if current_validator_identity_sha256:
        recorded_validator = _valid_digest(
            raw.get("review_validator_identity_sha256")
        )
        if recorded_validator != current_validator_identity_sha256:
            return None, "entry-local review validator identity is missing or stale"
    source_pin = raw.get("source_item")
    if not isinstance(source_pin, dict):
        return None, "entry-local coverage source pin is missing"
    if _valid_digest(entry.get("statement_sha256")) != _valid_digest(
        source_pin.get("source_target_sha256")
    ):
        return None, "coverage statement digest differs from its entry-local source pin"
    recorded_semantic = _valid_digest(entry.get("source_item_coverage_sha256"))
    if recorded_semantic and recorded_semantic != _valid_digest(
        source_pin.get("source_item_semantic_sha256")
    ):
        return None, "coverage source semantic digest differs from its entry-local source pin"
    return copy.deepcopy(source_pin), ""


def _coverage_source_pin_from_legacy(
    key: str,
    entry: Mapping[str, Any],
    *,
    previous_inventory: Mapping[str, Mapping[str, Any]] | None,
    previous_mode: str,
    previous_source_proof_fidelity: Mapping[str, Any] | None = None,
) -> tuple[dict[str, Any] | None, str]:
    if previous_inventory is None or not previous_mode:
        return None, "no entry-local semantic reuse pin; provide previous source map"
    old_item = previous_inventory.get(key)
    if old_item is None:
        return None, "coverage key does not identify a prior source item"
    pin, error = source_reuse_pin(
        old_item,
        previous_mode,
        source_proof_fidelity=previous_source_proof_fidelity,
    )
    if pin is None:
        return None, error
    expected_statement = _valid_digest(pin.get("source_target_sha256"))
    if _valid_digest(entry.get("statement_sha256")) != expected_statement:
        return None, "coverage statement digest differs from prior source target"
    recorded_semantic = _valid_digest(entry.get("source_item_coverage_sha256"))
    if recorded_semantic and recorded_semantic != _valid_digest(
        pin.get("source_item_semantic_sha256")
    ):
        return None, "coverage source semantic digest differs from prior source item"
    return pin, ""


def _coverage_disposition_matches_source_pin(
    entry: Mapping[str, Any], source_pin: Mapping[str, Any]
) -> str:
    """Reject stale correction/convention fields instead of rewriting them.

    The source semantic digest already covers these fields.  This explicit
    comparison prevents a coverage row with stale corrected-target metadata
    from being silently repaired merely because the canonical source map is
    current.
    """

    disposition = source_pin.get("source_target_disposition")
    if not isinstance(disposition, Mapping):
        return "coverage source pin has no corrected-target/convention disposition"
    kind = str(disposition.get("kind") or "").strip()
    coverage = str(entry.get("coverage") or "").strip().lower()
    if kind != "approved_corrected_target":
        if coverage == "covered_corrected_target" or str(
            entry.get("target_kind") or ""
        ).strip().lower() == "approved_corrected_target":
            return "ordinary/convention source item has corrected-target coverage metadata"
        return ""
    if coverage != "covered_corrected_target":
        return "corrected source item does not retain covered_corrected_target coverage"
    if str(entry.get("target_kind") or "").strip().lower() != "approved_corrected_target":
        return "corrected source item has no approved_corrected_target coverage pin"
    expected_fields = {
        "archival_statement_sha256": _valid_digest(
            disposition.get("archival_statement_sha256")
        ),
        "corrected_target_sha256": _valid_digest(
            disposition.get("corrected_target_sha256")
        ),
        "approval_artifact_sha256": _valid_digest(
            disposition.get("approval_artifact_sha256")
        ),
    }
    if not all(expected_fields.values()):
        return "corrected source pin has incomplete correction metadata"
    for field, expected in expected_fields.items():
        if _valid_digest(entry.get(field)) != expected:
            return f"coverage corrected-target field `{field}` is stale"
    if sorted(_string_list(entry.get("governing_defect_ids"))) != sorted(
        _string_list(disposition.get("governing_defect_ids"))
    ):
        return "coverage corrected-target governing defect ids are stale"
    if entry.get("archival_equivalence_claimed") is not False:
        return "coverage corrected-target item can not claim archival equivalence"
    return ""


def _rewrite_coverage_corrected_fields(
    entry: dict[str, Any], item: Mapping[str, Any]
) -> str:
    target = review_dashboard._source_item_corrected_target(dict(item))
    if target is None:
        if str(entry.get("coverage") or "").strip().lower() == "covered_corrected_target":
            return "ordinary source item is incorrectly marked covered_corrected_target"
        return ""
    if str(entry.get("coverage") or "").strip().lower() != "covered_corrected_target":
        return "corrected source item does not retain covered_corrected_target coverage"
    if str(entry.get("target_kind") or "").strip().lower() != "approved_corrected_target":
        return "corrected source item has no approved_corrected_target coverage pin"
    approval = target.get("approval")
    if not isinstance(approval, Mapping):
        return "corrected target has no approval artifact"
    entry.update(
        {
            "archival_statement_sha256": _valid_digest(item.get("statement_sha256")),
            "corrected_target_sha256": _valid_digest(target.get("corrected_target_sha256")),
            "governing_defect_ids": _string_list(target.get("governing_defect_ids")),
            "archival_equivalence_claimed": False,
            "approval_artifact_sha256": _valid_digest(approval.get("artifact_sha256")),
        }
    )
    return ""


def migrate_coverage_items(
    coverage_items: Mapping[str, Any],
    *,
    current_inventory: Mapping[str, Mapping[str, Any]],
    current_full_inventory: Mapping[str, Mapping[str, Any]] | None = None,
    current_mode: str,
    current_anchor_errors: Mapping[str, list[str]] | None,
    statement_bindings: Mapping[str, StatementBinding],
    current_source_proof_fidelity: Mapping[str, Any] | None = None,
    previous_inventory: Mapping[str, Mapping[str, Any]] | None = None,
    previous_mode: str = "",
    previous_source_proof_fidelity: Mapping[str, Any] | None = None,
    current_source_pin_cache: SourcePinCache | None = None,
    current_full_source_pin_cache: SourcePinCache | None = None,
    validator_identities: Mapping[str, str] | None = None,
    bootstrap_current: bool = False,
) -> tuple[dict[str, Any], dict[str, dict[str, Any]]]:
    """Migrate coverage entries only through already accepted statement rows."""

    output = copy.deepcopy(dict(coverage_items))
    decisions: dict[str, dict[str, Any]] = {}
    current_source_pin_cache = current_source_pin_cache or _source_pin_cache(
        current_inventory,
        current_mode,
        source_proof_fidelity=current_source_proof_fidelity,
    )
    if current_full_inventory is None:
        current_full_inventory = current_inventory
    current_full_source_pin_cache = (
        current_full_source_pin_cache
        or (
            current_source_pin_cache
            if current_full_inventory is current_inventory
            else _source_pin_cache(
                current_full_inventory,
                current_mode,
                source_proof_fidelity=current_source_proof_fidelity,
            )
        )
    )
    current_source_index = current_source_pin_cache.by_identity
    current_full_source_index = current_full_source_pin_cache.by_identity
    bindings_by_old_signature: dict[str, list[StatementBinding]] = {}
    for binding in statement_bindings.values():
        if binding.old_signature_sha256:
            bindings_by_old_signature.setdefault(binding.old_signature_sha256, []).append(binding)

    for raw_key, raw_entry in coverage_items.items():
        key = str(raw_key).strip()
        if not key or not isinstance(raw_entry, Mapping):
            continue
        entry = copy.deepcopy(dict(raw_entry))
        validator_identity = (
            _valid_digest(validator_identities.get(key))
            if validator_identities is not None
            else ""
        )
        if validator_identities is not None and not validator_identity:
            decisions[key] = {
                "accepted": False,
                "reason": "current review validator identity is missing or malformed",
            }
            continue
        pin, pin_error = _coverage_source_pin_from_embedded(
            entry,
            current_validator_identity_sha256=validator_identity,
        )
        if pin is None and REUSE_FIELD not in entry:
            pin, pin_error = _coverage_source_pin_from_legacy(
                key,
                entry,
                previous_inventory=previous_inventory,
                previous_mode=previous_mode,
                previous_source_proof_fidelity=previous_source_proof_fidelity,
            )
        if pin is None and REUSE_FIELD in entry:
            # Bootstrap records pins on genuinely unpinned current rows; it is
            # never a stale-pin override. In particular, a stale authenticated
            # identity cannot be replaced by looking up the same navigation key
            # and then used to justify deleting an out-of-scope entry.
            decisions[key] = {"accepted": False, "reason": pin_error}
            continue
        pin_was_bootstrapped = False
        if pin is None:
            if not bootstrap_current:
                decisions[key] = {"accepted": False, "reason": pin_error}
                continue
            current_item = current_full_inventory.get(key)
            if current_item is None:
                decisions[key] = {
                    "accepted": False,
                    "reason": "bootstrap coverage key does not identify a current source item",
                }
                continue
            cached_pin = current_full_source_pin_cache.by_key.get(key)
            if cached_pin is not None:
                pin = copy.deepcopy(cached_pin)
                pin_error = ""
                pin_was_bootstrapped = True
            else:
                pin = None
                pin_error = current_full_source_pin_cache.errors.get(
                    key, "current source item has no reusable semantic identity"
                )
            if pin is None:
                decisions[key] = {"accepted": False, "reason": pin_error}
                continue
        disposition_error = _coverage_disposition_matches_source_pin(entry, pin)
        if disposition_error:
            decisions[key] = {"accepted": False, "reason": disposition_error}
            continue
        identity = _stable_digest(pin)
        candidates = current_source_index.get(identity, [])
        if len(candidates) > 1:
            decisions[key] = {
                "accepted": False,
                "reason": (
                    "source semantic/quote identity is ambiguous in the canonical "
                    "selected coverage inventory"
                ),
            }
            continue
        if not candidates:
            if pin_was_bootstrapped:
                decisions[key] = {
                    "accepted": False,
                    "reason": (
                        "canonical exclusion requires an authenticated prior source pin; "
                        "current-key bootstrap cannot authorize removal"
                    ),
                }
                continue
            full_candidates = current_full_source_index.get(identity, [])
            if len(full_candidates) != 1:
                decisions[key] = {
                    "accepted": False,
                    "reason": (
                        "canonically excluded coverage item has no unique semantic/quote "
                        "identity in the full current source inventory"
                    ),
                }
                continue
            current_key, _current_item = full_candidates[0]
            if current_key in current_inventory:
                decisions[key] = {
                    "accepted": False,
                    "reason": (
                        "coverage identity belongs to the canonical selected inventory "
                        "but has no reusable selected source pin"
                    ),
                }
                continue
            if current_anchor_errors is None or current_anchor_errors.get(current_key):
                decisions[key] = {
                    "accepted": False,
                    "reason": (
                        "canonically excluded coverage source anchor is not byte-verified"
                    ),
                }
                continue
            decisions[key] = {
                "accepted": True,
                "semantic_exclusion": True,
                "disposition": COVERAGE_SEMANTIC_EXCLUSION,
                "current_source_item": current_key,
                "reason": (
                    "authenticated source identity uniquely rebinds to a full-inventory "
                    "item outside the canonical selected coverage inventory"
                ),
            }
            # The caller removes this provisional entry only after all other
            # accepted rows receive their current signature pins and the
            # canonical output-key migration is collision-free.
            continue
        current_key, current_item = candidates[0]
        if current_anchor_errors is None or current_anchor_errors.get(current_key):
            decisions[key] = {"accepted": False, "reason": "current source anchor is not byte-verified"}
            continue
        target_statement, target_digest = review_dashboard._source_item_coverage_statement(
            current_item
        )
        if not target_statement or _valid_digest(entry.get("statement_sha256")) != target_digest:
            decisions[key] = {"accepted": False, "reason": "coverage target statement digest changed"}
            continue
        rows = _string_list(entry.get("review_rows"))
        pins = entry.get("review_row_signature_sha256")
        zero_row_scope_exclusion = (
            str(entry.get("coverage") or "").strip().lower()
            == review_dashboard.USER_APPROVED_SCOPE_EXCLUSION
        )
        if zero_row_scope_exclusion:
            row_pin_error = bool(rows) or not isinstance(pins, Mapping) or bool(pins)
        else:
            row_pin_error = (
                not rows
                or not isinstance(pins, Mapping)
                or set(rows)
                != {str(name).strip() for name in pins if str(name).strip()}
            )
        if row_pin_error:
            decisions[key] = {"accepted": False, "reason": "coverage item has no exact review-row signature pins"}
            continue
        rebound_rows: list[str] = []
        for old_row in rows:
            old_signature = _valid_digest(pins.get(old_row))
            direct_binding = statement_bindings.get(old_row)
            if (
                direct_binding is not None
                and direct_binding.old_signature_sha256 == old_signature
            ):
                candidates_for_row = [direct_binding]
            else:
                candidates_for_row = bindings_by_old_signature.get(
                    old_signature, []
                )
            if len(candidates_for_row) != 1:
                decisions[key] = {
                    "accepted": False,
                    "reason": "coverage review-row signature does not identify one accepted statement item",
                }
                break
            binding = candidates_for_row[0]
            rebound_rows.append(binding.current_row_name)
        else:
            entry["review_rows"] = rebound_rows
            # Filled by the caller-provided per-row current signature index.
            decisions[key] = {
                "accepted": True,
                "current_source_item": current_key,
                **({"bootstrap_current": True} if pin_was_bootstrapped else {}),
            }
            entry["source_item_coverage_digest_schema"] = SOURCE_ITEM_COVERAGE_DIGEST_SCHEMA
            entry["source_item_coverage_sha256"] = _valid_digest(
                pin.get("source_item_semantic_sha256")
            )
            corrected_error = _rewrite_coverage_corrected_fields(entry, current_item)
            if corrected_error:
                decisions[key] = {"accepted": False, "reason": corrected_error}
                continue
            disposition_error = _coverage_disposition_matches_source_pin(entry, pin)
            if disposition_error:
                decisions[key] = {"accepted": False, "reason": disposition_error}
                continue
            entry[REUSE_FIELD] = {
                "schema": ENTRY_REUSE_SCHEMA,
                FORMALIZATION_REVIEW_PROTOCOL_FIELD: (
                    formalization_review_protocol_digest()
                ),
                "source_item": pin,
                "source_coverage_mode": current_mode,
            }
            if validator_identity:
                entry[REUSE_FIELD][
                    "review_validator_identity_sha256"
                ] = validator_identity
            # ``migrate_sidecars`` supplies and validates the actual current
            # signatures before committing this provisional row.
            output[key] = entry
            continue
        # A ``break`` above is represented by an existing rejected decision.
        continue
    return output, decisions


def _canonicalize_coverage_output_items(
    original_items: Mapping[str, Any],
    provisional_items: Mapping[str, Any],
    decisions: dict[str, dict[str, Any]],
    *,
    canonical_selected_keys: set[str],
) -> dict[str, Any]:
    """Rekey accepted coverage rows and remove only authenticated exclusions.

    Decisions are keyed by historical navigation ids.  A selected row's
    ``current_source_item`` is available only after its content pin uniquely
    rebinds, so canonicalization happens after semantic and row-signature
    validation.  Rejected or malformed entries remain byte-for-byte present;
    collisions propagate rejection rather than overwriting retained evidence.
    """

    original_by_key = {
        str(raw_key).strip(): copy.deepcopy(raw_item)
        for raw_key, raw_item in original_items.items()
        if str(raw_key).strip()
    }
    selected_candidates: dict[str, tuple[str, Any]] = {}
    authenticated_exclusions: set[str] = set()
    protected_keys = set(original_by_key)

    for old_key, decision in decisions.items():
        if not decision.get("accepted"):
            continue
        if decision.get("semantic_exclusion") is True:
            authenticated_exclusions.add(old_key)
            protected_keys.discard(old_key)
            continue
        current_key = str(decision.get("current_source_item") or "").strip()
        provisional = provisional_items.get(old_key)
        if (
            not current_key
            or current_key not in canonical_selected_keys
            or not isinstance(provisional, Mapping)
        ):
            decision.clear()
            decision.update(
                {
                    "accepted": False,
                    "reason": (
                        "accepted coverage migration has no exact canonical selected "
                        "output item"
                    ),
                }
            )
            continue
        selected_candidates[old_key] = (current_key, copy.deepcopy(dict(provisional)))
        protected_keys.discard(old_key)

    candidates_by_target: dict[str, list[str]] = {}
    for old_key, (current_key, _entry) in selected_candidates.items():
        candidates_by_target.setdefault(current_key, []).append(old_key)
    for current_key, old_keys in candidates_by_target.items():
        if len(old_keys) == 1:
            continue
        for old_key in old_keys:
            decisions[old_key] = {
                "accepted": False,
                "reason": (
                    "multiple authenticated coverage entries rebind to the same "
                    f"canonical selected source item {current_key!r}"
                ),
            }
            selected_candidates.pop(old_key, None)
            protected_keys.add(old_key)

    # A target occupied by rejected evidence cannot be overwritten. Rejection
    # may expose another protected historical key, so propagate to a fixed
    # point before constructing the output object.
    changed = True
    while changed:
        changed = False
        for old_key, (current_key, _entry) in list(selected_candidates.items()):
            if current_key in protected_keys and current_key != old_key:
                decisions[old_key] = {
                    "accepted": False,
                    "reason": (
                        "canonical coverage rekey would overwrite a rejected or "
                        f"unreviewed entry at {current_key!r}"
                    ),
                }
                selected_candidates.pop(old_key)
                protected_keys.add(old_key)
                changed = True

    output: dict[str, Any] = {
        key: copy.deepcopy(value)
        for key, value in original_by_key.items()
        if key in protected_keys
    }
    for old_key, (current_key, entry) in selected_candidates.items():
        output[current_key] = entry
        decisions[old_key]["output_source_item"] = current_key
    # Authenticated exclusions deliberately contribute no entry of their own;
    # an independently rebound selected item may legitimately reuse the same
    # navigation spelling, so names alone cannot support an assertion here.
    return output


def _current_signature_index(rows: Iterable[RowSnapshot]) -> dict[str, str]:
    out: dict[str, str] = {}
    seen: set[str] = set()
    ambiguous: set[str] = set()
    for row in rows:
        name = row.name
        if name in ambiguous:
            continue
        if name in seen:
            out.pop(name, None)
            ambiguous.add(name)
            continue
        seen.add(name)
        digest = _valid_digest(row.manifest.get("sha256"))
        if not digest:
            continue
        out[name] = digest
    return out


def _sidecar_item_key_error(
    statement_items: Mapping[object, Any],
    coverage_items: Mapping[object, Any],
) -> str:
    """Reject keys that downstream navigation normalization could conflate."""

    for lane, items in (
        ("statement", statement_items),
        ("coverage", coverage_items),
    ):
        normalized: list[str] = []
        for raw_key in items:
            if not isinstance(raw_key, str):
                return f"{lane} sidecar item key is not a string"
            key = raw_key.strip()
            normalized.append(key)
        if len(set(normalized)) != len(normalized):
            return f"{lane} sidecar item keys collide after normalization"
        if any(not key or key != raw_key for raw_key, key in zip(items, normalized)):
            return f"{lane} sidecar item key is empty or not exactly trimmed"
    return ""


def migrate_sidecars(
    statement_sidecar: Mapping[str, Any],
    coverage_sidecar: Mapping[str, Any],
    *,
    current_rows: Iterable[RowSnapshot],
    current_inventory: Mapping[str, Mapping[str, Any]],
    current_statement_inventory: Mapping[str, Mapping[str, Any]] | None = None,
    current_coverage_inventory: Mapping[str, Mapping[str, Any]] | None = None,
    current_mode: str,
    current_anchor_errors: Mapping[str, list[str]] | None,
    current_source_map: Mapping[str, Any] | None = None,
    canonical_coverage_projection_validated: bool = False,
    current_review_surface_sha256: str = "",
    current_source_proof_fidelity: Mapping[str, Any] | None = None,
    previous_inventory: Mapping[str, Mapping[str, Any]] | None = None,
    previous_mode: str = "",
    previous_rows: Iterable[RowSnapshot] | None = None,
    previous_source_proof_fidelity: Mapping[str, Any] | None = None,
    statement_validator_identities: Mapping[str, str] | None = None,
    coverage_validator_identities: Mapping[str, str] | None = None,
    bootstrap_current: bool = False,
    validate_statement: Callable[[dict[str, Any], RowSnapshot, Mapping[str, Mapping[str, Any]]], str]
    | None = None,
) -> tuple[dict[str, Any], dict[str, Any], dict[str, Any]]:
    """Return updated sidecars and a machine-readable per-item migration report."""

    statement_output = copy.deepcopy(dict(statement_sidecar))
    coverage_output = copy.deepcopy(dict(coverage_sidecar))
    current_rows = list(current_rows)
    if previous_mode and not source_coverage_modes_compatible(previous_mode, current_mode):
        return statement_output, coverage_output, {
            "schema": REUSE_SCHEMA,
            "statement": {},
            "coverage": {},
            "global_error": "source coverage mode changed incompatibly",
        }
    statement_items = statement_sidecar.get("items")
    coverage_items = coverage_sidecar.get("items")
    if not isinstance(statement_items, Mapping) or not isinstance(coverage_items, Mapping):
        return statement_output, coverage_output, {
            "schema": REUSE_SCHEMA,
            "statement": {},
            "coverage": {},
            "global_error": "sidecars do not contain item objects",
        }
    item_key_error = _sidecar_item_key_error(statement_items, coverage_items)
    if item_key_error:
        return statement_output, coverage_output, {
            "schema": REUSE_SCHEMA,
            "statement": {},
            "coverage": {},
            "global_error": item_key_error,
        }
    if current_source_map is not None and current_coverage_inventory is None:
        return statement_output, coverage_output, {
            "schema": REUSE_SCHEMA,
            "statement": {},
            "coverage": {},
            "global_error": (
                "aggregate coverage refresh requires the canonical selected "
                "coverage inventory"
            ),
        }
    statement_inventory = (
        current_inventory
        if current_statement_inventory is None
        else current_statement_inventory
    )
    missing_statement_parents = set(current_inventory) - set(statement_inventory)
    if missing_statement_parents or any(
        dict(statement_inventory[key]) != dict(current_inventory[key])
        for key in current_inventory
        if key in statement_inventory
    ):
        return statement_output, coverage_output, {
            "schema": REUSE_SCHEMA,
            "statement": {},
            "coverage": {},
            "global_error": (
                "statement-route inventory is not an exact extension of the "
                "canonical parent source inventory"
            ),
        }
    coverage_inventory = (
        current_inventory
        if current_coverage_inventory is None
        else current_coverage_inventory
    )
    coverage_keys = set(coverage_inventory)
    unexpected_coverage_keys = coverage_keys - set(current_inventory)
    if unexpected_coverage_keys:
        return statement_output, coverage_output, {
            "schema": REUSE_SCHEMA,
            "statement": {},
            "coverage": {},
            "global_error": (
                "selected coverage inventory is not a projection of the full "
                f"source inventory: {sorted(unexpected_coverage_keys)}"
            ),
        }
    for key in sorted(coverage_keys):
        selected_item = coverage_inventory.get(key)
        full_item = current_inventory.get(key)
        if not isinstance(selected_item, Mapping) or not isinstance(full_item, Mapping):
            return statement_output, coverage_output, {
                "schema": REUSE_SCHEMA,
                "statement": {},
                "coverage": {},
                "global_error": (
                    "selected coverage inventory contains a malformed source item "
                    f"at {key!r}"
                ),
            }
        if dict(selected_item) != dict(full_item):
            return statement_output, coverage_output, {
                "schema": REUSE_SCHEMA,
                "statement": {},
                "coverage": {},
                "global_error": (
                    "selected coverage inventory is not an exact projection of "
                    f"the full source inventory at {key!r}"
                ),
            }
    statement_source_pin_cache = _source_pin_cache(
        statement_inventory,
        current_mode,
        source_proof_fidelity=current_source_proof_fidelity,
    )
    full_source_pin_cache = _project_source_pin_cache(
        statement_source_pin_cache, set(current_inventory)
    )
    coverage_source_pin_cache = (
        full_source_pin_cache
        if coverage_keys == set(current_inventory)
        else _project_source_pin_cache(full_source_pin_cache, coverage_keys)
    )
    statement_output_items, statement_decisions, bindings = migrate_statement_items(
        statement_items,
        current_rows=current_rows,
        current_inventory=statement_inventory,
        current_mode=current_mode,
        current_anchor_errors=current_anchor_errors,
        current_source_proof_fidelity=current_source_proof_fidelity,
        previous_inventory=previous_inventory,
        previous_mode=previous_mode,
        previous_rows=previous_rows,
        previous_source_proof_fidelity=previous_source_proof_fidelity,
        current_source_pin_cache=statement_source_pin_cache,
        validator_identities=statement_validator_identities,
        bootstrap_current=bootstrap_current,
        validate_entry=validate_statement,
    )
    statement_output["items"] = statement_output_items

    # The coverage helper intentionally maps only through completed statement
    # migrations.  Fill its signature pins from the same current manifests and
    # reject an item if a row name is duplicate or absent.
    coverage_output_items, coverage_decisions = migrate_coverage_items(
        coverage_items,
        current_inventory=coverage_inventory,
        current_full_inventory=current_inventory,
        current_mode=current_mode,
        current_anchor_errors=current_anchor_errors,
        statement_bindings=bindings,
        current_source_proof_fidelity=current_source_proof_fidelity,
        previous_inventory=previous_inventory,
        previous_mode=previous_mode,
        previous_source_proof_fidelity=previous_source_proof_fidelity,
        current_source_pin_cache=coverage_source_pin_cache,
        current_full_source_pin_cache=full_source_pin_cache,
        validator_identities=coverage_validator_identities,
        bootstrap_current=bootstrap_current,
    )
    current_signatures = _current_signature_index(current_rows)
    for key, decision in list(coverage_decisions.items()):
        if not decision.get("accepted"):
            continue
        if decision.get("semantic_exclusion") is True:
            continue
        item = coverage_output_items.get(key)
        if not isinstance(item, dict):
            coverage_decisions[key] = {"accepted": False, "reason": "coverage migration lost its candidate"}
            continue
        rows = _string_list(item.get("review_rows"))
        if len(rows) != len(set(rows)) or any(row not in current_signatures for row in rows):
            coverage_decisions[key] = {"accepted": False, "reason": "current review-row signature is missing or ambiguous"}
            coverage_output_items[key] = copy.deepcopy(dict(coverage_items[key]))
            continue
        item["review_row_signature_sha256"] = {
            row: current_signatures[row] for row in rows
        }
    coverage_output_items = _canonicalize_coverage_output_items(
        coverage_items,
        coverage_output_items,
        coverage_decisions,
        canonical_selected_keys=coverage_keys,
    )
    coverage_output["items"] = coverage_output_items
    input_coverage_keys = {
        str(key).strip() for key in coverage_items if str(key).strip()
    }
    accepted_current_items = [
        str(decision.get("current_source_item") or "").strip()
        for decision in coverage_decisions.values()
        if decision.get("accepted") and decision.get("semantic_exclusion") is not True
    ]
    authenticated_exclusion_count = sum(
        decision.get("accepted") and decision.get("semantic_exclusion") is True
        for decision in coverage_decisions.values()
    )
    coverage_migration_complete = (
        bool(coverage_inventory) or canonical_coverage_projection_validated
    ) and (
        len(input_coverage_keys) == len(coverage_items)
        and set(coverage_decisions) == input_coverage_keys
        and all(
            bool(decision.get("accepted"))
            for decision in coverage_decisions.values()
        )
        and len(accepted_current_items) == len(coverage_inventory)
        and set(accepted_current_items) == coverage_keys
        and set(coverage_output_items) == coverage_keys
    )
    if coverage_migration_complete and current_source_map is not None:
        # Aggregate pins are only refreshed after an atomic, exact item-level
        # migration.  A partial reuse pass must leave the old aggregate receipt
        # stale so closeout cannot mistake incomplete coverage for a current
        # inventory review.
        coverage_output["source_coverage_mode"] = current_mode
        coverage_output["source_artifact_path"] = str(
            current_source_map.get("source_artifact_path") or ""
        ).strip()
        coverage_output["source_artifact_sha256"] = _valid_digest(
            current_source_map.get("source_artifact_sha256")
        )
        coverage_output["paper_statement_inventory_sha256"] = (
            review_dashboard.paper_coverage_inventory_digest(
                dict(coverage_inventory),
                mode=current_mode,
                statement_map_payload=dict(current_source_map),
            )
        )
        surface_digest = _valid_digest(current_review_surface_sha256)
        if surface_digest:
            coverage_output["review_surface_sha256"] = surface_digest
    report = {
        "schema": REUSE_SCHEMA,
        "statement": statement_decisions,
        "coverage": coverage_decisions,
        "accepted_statement_count": sum(
            bool(value.get("accepted")) for value in statement_decisions.values()
        ),
        "accepted_coverage_count": sum(
            bool(value.get("accepted")) for value in coverage_decisions.values()
        ),
        "authenticated_coverage_exclusion_count": authenticated_exclusion_count,
        "aggregate_coverage_receipt_refreshed": coverage_migration_complete
        and current_source_map is not None,
    }
    return statement_output, coverage_output, report


def _legacy_v4_coverage_metadata_error(
    payload: Mapping[str, Any], *, paper: str
) -> str:
    """Validate only the legacy format eligible for the explicit conversion."""

    if payload.get("schema") != 1:
        return "legacy v4 coverage sidecar schema is not 1"
    payload_paper = str(payload.get("paper") or "").strip()
    if payload_paper and payload_paper != paper:
        return "legacy v4 coverage sidecar belongs to a different paper"
    if (
        str(payload.get("prompt_version") or "").strip()
        != LEGACY_V4_COVERAGE_PROMPT_VERSION
    ):
        return "coverage sidecar is not the recognized legacy v4 format"
    audit_kind = str(payload.get("audit_kind") or "").strip()
    if audit_kind not in review_dashboard.APPROVED_PAPER_COVERAGE_AUDIT_KINDS:
        return "legacy v4 coverage audit_kind is not source-to-dashboard semantic evidence"
    if payload.get("source_grounded") is not True:
        return "legacy v4 coverage sidecar is not source-grounded"
    if payload.get("seed_scaffold") is True:
        return "legacy v4 coverage sidecar is a non-evidence scaffold"
    for field in ("validator", "validator_type", "validated_at"):
        if not str(payload.get(field) or "").strip():
            return f"legacy v4 coverage sidecar has no `{field}` metadata"
    if not isinstance(payload.get("items"), Mapping) or not payload.get("items"):
        return "legacy v4 coverage sidecar has no item judgments"
    return ""


def _source_items_by_target_digest(
    inventory: Mapping[str, Mapping[str, Any]],
) -> dict[str, list[tuple[str, dict[str, Any]]]]:
    """Index source items by target text only for legacy-v4 reconstruction.

    The v4 format did not carry a source semantic digest.  Its recorded target
    digest is therefore the sole historical content pointer.  We require it
    to select exactly one old item, then immediately replace it with the full
    source semantic/anchor identity; a map key is never used as a fallback.
    """

    index: dict[str, list[tuple[str, dict[str, Any]]]] = {}
    for raw_key, raw_item in inventory.items():
        if not isinstance(raw_item, Mapping):
            continue
        _statement, digest = review_dashboard._source_item_coverage_statement(
            dict(raw_item)
        )
        digest = _valid_digest(digest)
        if not digest:
            continue
        index.setdefault(digest, []).append((str(raw_key), dict(raw_item)))
    return index


def _legacy_v4_review_rows(
    entry: Mapping[str, Any],
) -> tuple[list[str] | None, str]:
    """Read an unambiguous direct-route list without accepting aliases."""

    raw_rows = entry.get("review_rows")
    if not isinstance(raw_rows, list) or not raw_rows:
        return None, "legacy v4 direct coverage has no review_rows list"
    rows = [str(row).strip() for row in raw_rows if str(row).strip()]
    if len(rows) != len(raw_rows) or len(rows) != len(set(rows)):
        return None, "legacy v4 review_rows must be a nonempty unique string list"
    return rows, ""


def _legacy_v4_row_binding(
    old_name: str,
    *,
    old_rows_by_name: Mapping[str, list[RowSnapshot]],
    old_row_errors: Mapping[str, list[str]],
    current_rows_by_semantic_identity: Mapping[str, list[RowSnapshot]],
    current_row_name_counts: Mapping[str, int],
) -> tuple[dict[str, str] | None, str]:
    """Prove one legacy row navigates to exactly one unchanged current row."""

    if old_row_errors.get(old_name):
        return None, "; ".join(old_row_errors[old_name])
    old_candidates = old_rows_by_name.get(old_name, [])
    if len(old_candidates) != 1:
        return None, "legacy review row name is missing or ambiguous in previous cache"
    old_row = old_candidates[0]
    old_identity, old_signature, old_structure, old_error = _semantic_row_identity(
        old_row
    )
    if old_error:
        return None, f"previous review-cache {old_error}"
    current_candidates = current_rows_by_semantic_identity.get(old_identity, [])
    if len(current_candidates) != 1:
        return None, "semantic Lean row identity is missing or ambiguous in current review surface"
    current_row = current_candidates[0]
    if current_row_name_counts.get(current_row.name) != 1:
        return None, "current review-row name is missing or ambiguous"
    current_identity, current_signature, current_structure, current_error = _semantic_row_identity(
        current_row
    )
    if current_error:
        return None, f"current review-surface {current_error}"
    if old_identity != current_identity or old_structure != current_structure:
        return None, "old/current elaborated manifest atom/ref/role structure changed"
    paper_digest = review_dashboard.statement_digest(old_row.paper_statement)
    if paper_digest != review_dashboard.statement_digest(current_row.paper_statement):
        return None, "dashboard paper statement changed"
    return {
        "legacy_review_row": old_row.name,
        "current_review_row": current_row.name,
        "old_lean_signature_sha256": old_signature,
        "current_lean_signature_sha256": current_signature,
        "manifest_structure_sha256": old_structure,
        "semantic_row_identity_sha256": old_identity,
        "paper_statement_sha256": paper_digest,
    }, ""


def migrate_legacy_v4_coverage(
    legacy_coverage: Mapping[str, Any],
    *,
    legacy_v4_opt_in: bool,
    paper: str,
    folder: Path,
    current_source_map: Mapping[str, Any],
    previous_source_map: Mapping[str, Any] | None,
    previous_review_cache: Mapping[str, Any] | None,
    current_rows: Iterable[RowSnapshot],
    current_review_surface_sha256: str,
    current_anchor_errors: Mapping[str, list[str]] | None,
    current_source_proof_fidelity: Mapping[str, Any] | None = None,
    previous_source_proof_fidelity: Mapping[str, Any] | None = None,
) -> tuple[dict[str, Any] | None, dict[str, Any]]:
    """Convert a legacy v4 coverage audit only through independently pinned IDs.

    This is intentionally atomic.  Unlike ordinary item-level v10 refreshes,
    the legacy sidecar has no row signature pins to leave in place on a partial
    failure.  Returning ``None`` on any rejected entry prevents ``--write``
    from replacing useful v4 evidence with a deceptively incomplete v5 file.
    """

    report: dict[str, Any] = {
        "schema": LEGACY_V4_MIGRATION_SCHEMA,
        "migration": "legacy_v4_coverage_to_current_v5",
        "statement_contract": review_dashboard.REQUIRED_LLM_STATEMENT_PROMPT_VERSION,
        "coverage_contract": review_dashboard.REQUIRED_LLM_PAPER_COVERAGE_PROMPT_VERSION,
        "items": {},
    }
    if not legacy_v4_opt_in:
        report["global_error"] = (
            "legacy v4 coverage migration requires explicit --migrate-legacy-v4-coverage opt-in"
        )
        return None, report
    metadata_error = _legacy_v4_coverage_metadata_error(legacy_coverage, paper=paper)
    if metadata_error:
        report["global_error"] = metadata_error
        return None, report
    if not isinstance(previous_source_map, Mapping) or not previous_source_map:
        report["global_error"] = "legacy v4 migration requires a previous source-map snapshot"
        return None, report
    if not isinstance(previous_review_cache, Mapping) or not previous_review_cache:
        report["global_error"] = "legacy v4 migration requires a previous review-cache snapshot"
        return None, report
    if current_anchor_errors is None:
        report["global_error"] = "legacy v4 migration requires current byte-anchor validation"
        return None, report
    current_mode, current_mode_error = source_coverage_mode_from_map(current_source_map)
    if current_mode_error:
        report["global_error"] = f"current source coverage mode is invalid: {current_mode_error}"
        return None, report
    previous_mode, previous_mode_error = source_coverage_mode_from_map(previous_source_map)
    if previous_mode_error:
        report["global_error"] = f"previous source coverage mode is invalid: {previous_mode_error}"
        return None, report
    if not source_coverage_modes_compatible(previous_mode, current_mode):
        report["global_error"] = "source coverage mode changed incompatibly"
        return None, report
    current_surface_digest = _valid_digest(current_review_surface_sha256)
    if not current_surface_digest:
        report["global_error"] = "current review surface has no valid digest"
        return None, report

    current_full_inventory = inventory_from_source_map(folder, current_source_map)
    previous_full_inventory = inventory_from_source_map(folder, previous_source_map)
    current_inventory = filter_source_inventory_for_coverage(
        current_full_inventory,
        current_mode,
        declared_environment_kinds=source_named_result_environment_kinds_from_map(
            current_source_map
        ),
    )
    previous_inventory = filter_source_inventory_for_coverage(
        previous_full_inventory,
        previous_mode,
        declared_environment_kinds=source_named_result_environment_kinds_from_map(
            previous_source_map
        ),
    )
    if not current_inventory:
        report["global_error"] = "current source map has no in-scope source items"
        return None, report
    if not previous_inventory:
        report["global_error"] = "previous source-map snapshot has no in-scope source items"
        return None, report
    old_rows_by_name, old_row_errors, old_cache_error = _legacy_v4_rows_from_review_cache(
        previous_review_cache
    )
    if old_cache_error:
        report["global_error"] = old_cache_error
        return None, report
    current_rows = list(current_rows)
    if not current_rows:
        report["global_error"] = "current review surface has no rows"
        return None, report
    current_rows_by_semantic_identity = _unique_by_semantic_row_identity(current_rows)
    current_row_name_counts: dict[str, int] = {}
    for row in current_rows:
        current_row_name_counts[row.name] = current_row_name_counts.get(row.name, 0) + 1
    current_source_index, _current_source_errors = _source_pin_index(
        current_inventory,
        current_mode,
        source_proof_fidelity=current_source_proof_fidelity,
    )
    previous_by_target = _source_items_by_target_digest(previous_inventory)
    raw_items = legacy_coverage.get("items")
    assert isinstance(raw_items, Mapping)
    output_items: dict[str, dict[str, Any]] = {}
    used_current_source_keys: set[str] = set()

    for raw_key, raw_entry in raw_items.items():
        legacy_key = str(raw_key).strip()
        decision_key = legacy_key or f"<invalid-key-{len(report['items'])}>"
        if not legacy_key or not isinstance(raw_entry, Mapping):
            report["items"][decision_key] = {
                "accepted": False,
                "reason": "legacy v4 coverage item key or object is invalid",
            }
            continue
        entry = dict(raw_entry)
        coverage = review_dashboard._normalize_paper_coverage_judgment(
            entry.get("coverage")
            or entry.get("judgment")
            or entry.get("verdict")
            or entry.get("status")
        )
        if coverage not in LEGACY_V4_DIRECT_COVERAGE_JUDGMENTS:
            report["items"][legacy_key] = {
                "accepted": False,
                "reason": (
                    "legacy v4 coverage judgment has no direct signed review-row route; "
                    "re-audit it under the current contract"
                ),
            }
            continue
        reason = str(entry.get("reason") or "").strip()
        source_evidence = str(entry.get("source_evidence") or "").strip()
        if not reason or not source_evidence:
            report["items"][legacy_key] = {
                "accepted": False,
                "reason": "legacy v4 direct coverage lacks reason or source_evidence",
            }
            continue
        legacy_target_digest = _valid_digest(entry.get("statement_sha256"))
        if not legacy_target_digest:
            report["items"][legacy_key] = {
                "accepted": False,
                "reason": "legacy v4 coverage item has no exact source statement digest",
            }
            continue
        previous_candidates = previous_by_target.get(legacy_target_digest, [])
        if len(previous_candidates) != 1:
            report["items"][legacy_key] = {
                "accepted": False,
                "reason": (
                    "legacy source statement digest does not identify exactly one "
                    "previous source item"
                ),
            }
            continue
        previous_key, previous_item = previous_candidates[0]
        previous_pin, previous_pin_error = source_reuse_pin(
            previous_item,
            previous_mode,
            source_proof_fidelity=previous_source_proof_fidelity,
        )
        if previous_pin is None:
            report["items"][legacy_key] = {
                "accepted": False,
                "reason": f"previous source item has no semantic/anchor pin: {previous_pin_error}",
            }
            continue
        if _valid_digest(previous_pin.get("source_target_sha256")) != legacy_target_digest:
            report["items"][legacy_key] = {
                "accepted": False,
                "reason": "legacy source statement digest differs from its previous source item",
            }
            continue
        disposition_error = _coverage_disposition_matches_source_pin(entry, previous_pin)
        if disposition_error:
            report["items"][legacy_key] = {
                "accepted": False,
                "reason": disposition_error,
            }
            continue
        current_candidates = current_source_index.get(_stable_digest(previous_pin), [])
        if len(current_candidates) != 1:
            report["items"][legacy_key] = {
                "accepted": False,
                "reason": "source semantic/quote identity is missing or ambiguous in current map",
            }
            continue
        current_key, current_item = current_candidates[0]
        if current_key in used_current_source_keys:
            report["items"][legacy_key] = {
                "accepted": False,
                "reason": "two legacy coverage items map to one current source item",
            }
            continue
        if current_anchor_errors.get(current_key):
            report["items"][legacy_key] = {
                "accepted": False,
                "reason": "current source anchor is not byte-verified",
            }
            continue
        _current_statement, current_target_digest = (
            review_dashboard._source_item_coverage_statement(current_item)
        )
        if _valid_digest(current_target_digest) != legacy_target_digest:
            report["items"][legacy_key] = {
                "accepted": False,
                "reason": "current source target statement digest changed",
            }
            continue
        review_rows, review_rows_error = _legacy_v4_review_rows(entry)
        if review_rows is None:
            report["items"][legacy_key] = {
                "accepted": False,
                "reason": review_rows_error,
            }
            continue
        row_bindings: list[dict[str, str]] = []
        current_review_rows: list[str] = []
        row_error = ""
        for old_name in review_rows:
            binding, binding_error = _legacy_v4_row_binding(
                old_name,
                old_rows_by_name=old_rows_by_name,
                old_row_errors=old_row_errors,
                current_rows_by_semantic_identity=current_rows_by_semantic_identity,
                current_row_name_counts=current_row_name_counts,
            )
            if binding is None:
                row_error = binding_error
                break
            current_name = binding["current_review_row"]
            if current_name in current_review_rows:
                row_error = "two legacy rows map to one current review row"
                break
            row_bindings.append(binding)
            current_review_rows.append(current_name)
        if row_error:
            report["items"][legacy_key] = {"accepted": False, "reason": row_error}
            continue
        current_pin, current_pin_error = source_reuse_pin(
            current_item,
            current_mode,
            source_proof_fidelity=current_source_proof_fidelity,
        )
        if current_pin is None or _stable_digest(current_pin) != _stable_digest(previous_pin):
            report["items"][legacy_key] = {
                "accepted": False,
                "reason": (
                    "current source semantic/quote identity cannot be reproduced"
                    if current_pin is None
                    else "source semantic/quote identity changed"
                ),
            }
            continue
        migrated: dict[str, Any] = {
            "coverage": coverage,
            "review_rows": current_review_rows,
            "review_row_signature_sha256": {
                binding["current_review_row"]: binding["current_lean_signature_sha256"]
                for binding in row_bindings
            },
            "reason": reason,
            "source_evidence": source_evidence,
            "dashboard_evidence": str(entry.get("dashboard_evidence") or "").strip(),
            "statement_sha256": legacy_target_digest,
            "source_item_coverage_digest_schema": SOURCE_ITEM_COVERAGE_DIGEST_SCHEMA,
            "source_item_coverage_sha256": source_item_coverage_sha256(
                current_item, current_mode
            ),
        }
        source_scope_judgment = str(entry.get("source_scope_judgment") or "").strip()
        if source_scope_judgment:
            migrated["source_scope_judgment"] = source_scope_judgment
        for field in (
            "target_kind",
            "archival_statement_sha256",
            "corrected_target_sha256",
            "governing_defect_ids",
            "archival_equivalence_claimed",
        ):
            if field in entry:
                migrated[field] = copy.deepcopy(entry[field])
        corrected_error = _rewrite_coverage_corrected_fields(migrated, current_item)
        if corrected_error:
            report["items"][legacy_key] = {"accepted": False, "reason": corrected_error}
            continue
        disposition_error = _coverage_disposition_matches_source_pin(migrated, current_pin)
        if disposition_error:
            report["items"][legacy_key] = {
                "accepted": False,
                "reason": disposition_error,
            }
            continue
        migrated[REUSE_FIELD] = {
            "schema": ENTRY_REUSE_SCHEMA,
            FORMALIZATION_REVIEW_PROTOCOL_FIELD: (
                formalization_review_protocol_digest()
            ),
            "review_validator_identity_sha256": _stable_digest(
                {
                    "schema": REVIEW_VALIDATOR_IDENTITY_SCHEMA,
                    "prompt_version": (
                        review_dashboard.REQUIRED_LLM_PAPER_COVERAGE_PROMPT_VERSION
                    ),
                    "validator": str(legacy_coverage.get("validator") or "").strip(),
                    "validator_type": str(
                        legacy_coverage.get("validator_type") or ""
                    ).strip(),
                }
            ),
            "source_item": copy.deepcopy(current_pin),
            "source_coverage_mode": current_mode,
            LEGACY_V4_MIGRATION_FIELD: {
                "schema": LEGACY_V4_MIGRATION_SCHEMA,
                "legacy_prompt_version": LEGACY_V4_COVERAGE_PROMPT_VERSION,
                "previous_source_item": previous_key,
                "current_source_item": current_key,
                "source_target_sha256": legacy_target_digest,
                "source_item_semantic_sha256": current_pin[
                    "source_item_semantic_sha256"
                ],
                "source_anchor_quote_identity_sha256": current_pin[
                    "source_anchor_quote_identity_sha256"
                ],
                "review_rows": row_bindings,
            },
        }
        output_items[current_key] = migrated
        used_current_source_keys.add(current_key)
        report["items"][legacy_key] = {
            "accepted": True,
            "current_source_item": current_key,
            "source_rebinding": f"{previous_key} -> {current_key}",
            "review_row_rebindings": [
                f"{binding['legacy_review_row']} -> {binding['current_review_row']}"
                for binding in row_bindings
            ],
        }

    accepted = sum(
        bool(decision.get("accepted")) for decision in report["items"].values()
    )
    rejected = len(report["items"]) - accepted
    report["accepted_item_count"] = accepted
    report["rejected_item_count"] = rejected
    if rejected:
        report["global_error"] = (
            "legacy v4 migration is atomic; one or more item identities could not be verified"
        )
        return None, report
    output = {
        "schema": 1,
        "paper": paper,
        "prompt_version": review_dashboard.REQUIRED_LLM_PAPER_COVERAGE_PROMPT_VERSION,
        "audit_kind": str(legacy_coverage.get("audit_kind") or "").strip(),
        "source_grounded": True,
        "seed_scaffold": False,
        "validator": str(legacy_coverage.get("validator") or "").strip(),
        "validator_type": str(legacy_coverage.get("validator_type") or "").strip(),
        "validated_at": str(legacy_coverage.get("validated_at") or "").strip(),
        "comment": (
            "Legacy v4 source-to-dashboard judgments migrated only after exact "
            "source-item and old/current elaborated Lean-row identity verification. "
            + str(legacy_coverage.get("comment") or "").strip()
        ).strip(),
        "source_coverage_mode": current_mode,
        "source_artifact_path": str(
            current_source_map.get("source_artifact_path") or ""
        ).strip(),
        "source_artifact_sha256": _valid_digest(
            current_source_map.get("source_artifact_sha256")
        ),
        "paper_statement_inventory_sha256": review_dashboard.paper_coverage_inventory_digest(
            current_inventory,
            mode=current_mode,
            statement_map_payload=dict(current_source_map),
        ),
        "review_surface_sha256": current_surface_digest,
        LEGACY_V4_MIGRATION_FIELD: {
            "schema": LEGACY_V4_MIGRATION_SCHEMA,
            "legacy_coverage_sha256": _stable_digest(legacy_coverage),
            "previous_source_map_sha256": _stable_digest(previous_source_map),
            "previous_review_cache_sha256": _stable_digest(previous_review_cache),
            "current_source_map_sha256": _stable_digest(current_source_map),
            "previous_source_coverage_mode": previous_mode,
            "current_source_coverage_mode": current_mode,
            "accepted_item_count": accepted,
            "identity_rule": (
                "exact source target plus semantic/anchor pin; name-independent "
                "elaborated manifest structure; verified old/current signatures; "
                "unchanged paper-facing row statement"
            ),
        },
        "items": output_items,
    }
    return output, report


def _load_json(path: Path) -> dict[str, Any]:
    try:
        payload = json.loads(path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError):
        return {}
    return payload if isinstance(payload, dict) else {}


def review_validator_identities(
    payload: Mapping[str, Any], *, expected_prompt_version: str
) -> tuple[dict[str, str], dict[str, str]]:
    """Return exact per-item reviewer identities and fail-closed errors.

    Item metadata inherits the sidecar envelope in the same way as the review
    loader.  Timestamps are required provenance but are not identity: changing
    presentation time alone does not change who reviewed under which protocol.
    The semantic judgment itself remains pinned by the entry-local source and
    Lean identities.
    """

    raw_items = payload.get("items")
    if not isinstance(raw_items, Mapping):
        return {}, {"<sidecar>": "sidecar has no item object"}
    identities: dict[str, str] = {}
    errors: dict[str, str] = {}
    for raw_key, raw_item in raw_items.items():
        key = str(raw_key).strip()
        if not key:
            continue
        if not isinstance(raw_item, Mapping):
            errors[key] = "review item is not an object"
            continue
        prompt_version = str(
            raw_item.get("prompt_version") or payload.get("prompt_version") or ""
        ).strip()
        validator = str(
            raw_item.get("validator")
            or raw_item.get("model")
            or raw_item.get("judge")
            or raw_item.get("agent")
            or raw_item.get("generator")
            or payload.get("validator")
            or payload.get("model")
            or payload.get("judge")
            or payload.get("agent")
            or payload.get("generator")
            or ""
        ).strip()
        validator_type = str(
            raw_item.get("validator_type")
            or raw_item.get("generator_type")
            or payload.get("validator_type")
            or payload.get("generator_type")
            or ""
        ).strip()
        validated_at = str(
            raw_item.get("validated_at")
            or raw_item.get("timestamp")
            or raw_item.get("generated_at")
            or payload.get("validated_at")
            or payload.get("timestamp")
            or payload.get("generated_at")
            or ""
        ).strip()
        missing = [
            label
            for label, value in (
                ("validator", validator),
                ("validator_type", validator_type),
                ("validated_at", validated_at),
            )
            if not value
        ]
        if prompt_version != expected_prompt_version:
            errors[key] = "review prompt version is missing or not current"
            continue
        if missing:
            errors[key] = "review metadata is missing " + ", ".join(missing)
            continue
        identities[key] = _stable_digest(
            {
                "schema": REVIEW_VALIDATOR_IDENTITY_SCHEMA,
                "prompt_version": prompt_version,
                "validator": validator,
                "validator_type": validator_type,
            }
        )
    return identities, errors


def _current_anchor_errors(folder: Path, keys: Iterable[str]) -> dict[str, list[str]]:
    """Run the repository's byte validator for exactly proposed source items."""

    return review_dashboard._semantic_reuse_source_anchor_errors(folder, keys)


def _statement_validator(
    entry: dict[str, Any],
    row: RowSnapshot,
    inventory: Mapping[str, Mapping[str, Any]],
    *,
    include_direct_expressions: bool = False,
) -> str:
    normalized_inventory = {str(key): dict(value) for key, value in inventory.items()}
    ledger_error = review_dashboard.semantic_obligation_ledger_error(
        entry,
        row.manifest,
        require_source_definition_semantics_review=bool(
            review_dashboard.direct_source_definition_route_keys(
                entry,
                inventory=normalized_inventory,
                include_direct_expressions=include_direct_expressions,
            )
        ),
    )
    if ledger_error:
        return f"statement obligation ledger is invalid after migration: {ledger_error}"
    route_error = review_dashboard.source_route_pin_error(
        entry,
        inventory=normalized_inventory,
        require_statement_target=True,
        require_verbatim_source_inputs=(
            review_dashboard.statement_review_requires_verbatim_source_inputs(
                entry
            )
        ),
    )
    if route_error:
        return f"source route pins are invalid after migration: {route_error}"
    return ""


def _sidecar_is_v10_statement(payload: Mapping[str, Any]) -> bool:
    return (
        payload.get("schema") == 1
        and str(payload.get("prompt_version") or "").strip()
        == review_dashboard.REQUIRED_LLM_STATEMENT_PROMPT_VERSION
        and isinstance(payload.get("items"), Mapping)
    )


def _sidecar_is_current_coverage_schema(payload: Mapping[str, Any]) -> bool:
    return (
        payload.get("schema") == 1
        and str(payload.get("prompt_version") or "").strip()
        == review_dashboard.REQUIRED_LLM_PAPER_COVERAGE_PROMPT_VERSION
        and isinstance(payload.get("items"), Mapping)
    )


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--paper", required=True, help="Paper folder name under papers/.")
    parser.add_argument(
        "--previous-source-map",
        type=Path,
        help="Historical paper_statement_map.json snapshot for legacy sidecars.",
    )
    parser.add_argument(
        "--previous-review-cache",
        type=Path,
        help="Historical .review_traces/paper_interface_cache.json for legacy sidecars.",
    )
    parser.add_argument(
        "--previous-source-proof-fidelity",
        type=Path,
        help=(
            "Historical source_proof_fidelity.json for legacy source-map items "
            "that cite model_convention_ids."
        ),
    )
    parser.add_argument(
        "--migrate-legacy-v4-coverage",
        action="store_true",
        help=(
            "Explicitly and atomically migrate the tracked legacy v4 "
            "paper_coverage_llm.json to the current statement-v10/coverage-v5 "
            "contract. Requires both --previous-source-map and "
            "--previous-review-cache; names only navigate snapshots, while every "
            "source item and Lean row must rebind by verified content identity."
        ),
    )
    parser.add_argument(
        "--write",
        action="store_true",
        help="Write only accepted item migrations in place. Default is a dry run.",
    )
    parser.add_argument(
        "--bootstrap-current",
        action="store_true",
        help=(
            "Record entry-local reuse pins only for already current, fully valid "
            "v10 rows. This never refreshes stale evidence."
        ),
    )
    parser.add_argument(
        "--report",
        type=Path,
        help="Optional path for the JSON migration report (stdout otherwise).",
    )
    args = parser.parse_args()

    folder = ROOT / "papers" / args.paper
    statement_path = folder / "audit" / "statement_match_llm.json"
    coverage_path = folder / "audit" / "paper_coverage_llm.json"
    current_map_path = folder / "audit" / "paper_statement_map.json"
    current_fidelity_path = folder / "audit" / "source_proof_fidelity.json"
    statement_sidecar = _load_json(statement_path)
    coverage_sidecar = _load_json(coverage_path)
    current_map = _load_json(current_map_path)
    current_source_proof_fidelity = _load_json(current_fidelity_path)
    statement_validator_identities, statement_validator_errors = (
        review_validator_identities(
            statement_sidecar,
            expected_prompt_version=review_dashboard.REQUIRED_LLM_STATEMENT_PROMPT_VERSION,
        )
    )
    coverage_validator_identities, coverage_validator_errors = (
        review_validator_identities(
            coverage_sidecar,
            expected_prompt_version=(
                review_dashboard.REQUIRED_LLM_PAPER_COVERAGE_PROMPT_VERSION
            ),
        )
    )
    previous_map = _load_json(args.previous_source_map) if args.previous_source_map else {}
    previous_cache = _load_json(args.previous_review_cache) if args.previous_review_cache else {}
    previous_source_proof_fidelity = (
        _load_json(args.previous_source_proof_fidelity)
        if args.previous_source_proof_fidelity
        else {}
    )
    if args.migrate_legacy_v4_coverage:
        if args.bootstrap_current:
            raise SystemExit(
                "--migrate-legacy-v4-coverage cannot be combined with --bootstrap-current"
            )
        if not args.previous_source_map or not args.previous_review_cache:
            raise SystemExit(
                "--migrate-legacy-v4-coverage requires both --previous-source-map "
                "and --previous-review-cache"
            )
        if not previous_map or not previous_cache:
            raise SystemExit(
                "legacy v4 migration could not load both previous source-map and "
                "review-cache snapshots"
            )
        if not folder.is_dir() or not current_map:
            raise SystemExit("current paper folder or paper statement map is unavailable")
        current_review_items = review_dashboard.review_items_for_paper(
            folder,
            use_cache=True,
            render_images=False,
            persist_cache_rebind=args.write,
        )
        current_rows = row_snapshots_from_dashboard(current_review_items)
        current_full_inventory = inventory_from_source_map(folder, current_map)
        migrated_coverage, report = migrate_legacy_v4_coverage(
            coverage_sidecar,
            legacy_v4_opt_in=True,
            paper=args.paper,
            folder=folder,
            current_source_map=current_map,
            previous_source_map=previous_map,
            previous_review_cache=previous_cache,
            current_rows=current_rows,
            current_review_surface_sha256=review_dashboard.review_surface_digest(
                current_review_items
            ),
            current_anchor_errors=_current_anchor_errors(
                folder, current_full_inventory.keys()
            ),
            current_source_proof_fidelity=current_source_proof_fidelity or None,
            previous_source_proof_fidelity=previous_source_proof_fidelity or None,
        )
        report.update(
            {
                "paper": args.paper,
                "dry_run": not args.write,
                "legacy_v4_opt_in": True,
                "coverage_path": str(coverage_path.relative_to(ROOT)),
                "previous_source_map": str(args.previous_source_map),
                "previous_review_cache": str(args.previous_review_cache),
            }
        )
        encoded = json.dumps(report, indent=2, sort_keys=True) + "\n"
        if args.report:
            args.report.write_text(encoded, encoding="utf-8")
        else:
            print(encoded, end="")
        if migrated_coverage is None:
            return 2
        if args.write:
            coverage_path.write_text(
                json.dumps(migrated_coverage, indent=2, sort_keys=False) + "\n",
                encoding="utf-8",
            )
        return 0
    if not folder.is_dir() or not _sidecar_is_v10_statement(statement_sidecar):
        raise SystemExit("current statement sidecar is not a populated v10 statement-match sidecar")
    if not _sidecar_is_current_coverage_schema(coverage_sidecar):
        raise SystemExit("current coverage sidecar is not a current v10 coverage sidecar")
    if not current_map:
        raise SystemExit("current paper statement map is unavailable")
    if bool(previous_map) != bool(previous_cache):
        raise SystemExit(
            "legacy migration requires both --previous-source-map and --previous-review-cache"
        )
    if args.previous_source_proof_fidelity and not previous_map:
        raise SystemExit(
            "--previous-source-proof-fidelity requires both --previous-source-map "
            "and --previous-review-cache"
        )
    current_review_items = review_dashboard.review_items_for_paper(
        folder,
        use_cache=True,
        render_images=False,
        persist_cache_rebind=args.write,
    )
    current_rows = row_snapshots_from_dashboard(current_review_items)
    current_inventory = inventory_from_source_map(folder, current_map)
    current_statement_inventory = dict(current_inventory)
    for component_inventory in (
        review_dashboard.paper_source_component_route_inventory(folder),
        review_dashboard.paper_source_definition_component_route_inventory(folder),
    ):
        for key, item in component_inventory.items():
            prior = current_statement_inventory.get(key)
            if prior is not None and dict(prior) != dict(item):
                raise SystemExit(
                    "current statement component inventory has a conflicting "
                    f"content identity at {key!r}"
                )
            current_statement_inventory[key] = item
    current_mode, current_mode_error = source_coverage_mode_from_map(current_map)
    if current_mode_error:
        raise SystemExit(f"current source coverage mode is invalid: {current_mode_error}")
    current_coverage_inventory, coverage_projection_error = (
        canonical_coverage_inventory_projection(
            folder,
            current_inventory=current_inventory,
            current_mode=current_mode,
        )
    )
    if coverage_projection_error:
        raise SystemExit(coverage_projection_error)
    previous_inventory = inventory_from_source_map(folder, previous_map) if previous_map else None
    previous_mode = source_coverage_mode_from_map(previous_map)[0] if previous_map else ""
    previous_rows = row_snapshots_from_cache(previous_cache) if previous_cache else None
    anchor_errors = _current_anchor_errors(folder, current_inventory.keys())
    for key, item in current_statement_inventory.items():
        parent = str(item.get("source_component_of") or "").strip()
        if parent and parent in anchor_errors:
            anchor_errors[key] = list(anchor_errors[parent])
    updated_statement, updated_coverage, report = migrate_sidecars(
        statement_sidecar,
        coverage_sidecar,
        current_rows=current_rows,
        current_inventory=current_inventory,
        current_statement_inventory=current_statement_inventory,
        current_coverage_inventory=current_coverage_inventory,
        current_mode=current_mode,
        current_anchor_errors=anchor_errors,
        current_source_map=current_map,
        canonical_coverage_projection_validated=True,
        current_review_surface_sha256=review_dashboard.review_surface_digest(
            current_review_items
        ),
        current_source_proof_fidelity=current_source_proof_fidelity or None,
        previous_inventory=previous_inventory,
        previous_mode=previous_mode,
        previous_rows=previous_rows,
        previous_source_proof_fidelity=previous_source_proof_fidelity or None,
        statement_validator_identities=statement_validator_identities,
        coverage_validator_identities=coverage_validator_identities,
        validate_statement=lambda entry, row, inventory: _statement_validator(
            entry,
            row,
            inventory,
            include_direct_expressions=(
                review_dashboard.llm_direct_expression_semantics_review_required(
                    folder
                )
            ),
        ),
        bootstrap_current=args.bootstrap_current,
    )
    report.update(
        {
            "paper": args.paper,
            "dry_run": not args.write,
            "bootstrap_current": bool(args.bootstrap_current),
            "statement_path": str(statement_path.relative_to(ROOT)),
            "coverage_path": str(coverage_path.relative_to(ROOT)),
            "source_proof_fidelity_path": str(current_fidelity_path.relative_to(ROOT)),
            "validator_identity_errors": {
                "statement": statement_validator_errors,
                "coverage": coverage_validator_errors,
            },
        }
    )
    encoded = json.dumps(report, indent=2, sort_keys=True) + "\n"
    if args.report:
        args.report.write_text(encoded, encoding="utf-8")
    else:
        print(encoded, end="")
    if args.write:
        if updated_statement != statement_sidecar:
            statement_path.write_text(
                json.dumps(updated_statement, indent=2, sort_keys=False) + "\n",
                encoding="utf-8",
            )
        if updated_coverage != coverage_sidecar:
            coverage_path.write_text(
                json.dumps(updated_coverage, indent=2, sort_keys=False) + "\n",
                encoding="utf-8",
            )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
