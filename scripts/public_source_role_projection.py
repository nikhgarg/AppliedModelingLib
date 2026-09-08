#!/usr/bin/env python3
"""Authenticate deterministic public projections of accepted source roles.

The accepted obligation graph binds the private source-role digest.  A public
source map may deliberately withhold the approval reference and local source
locator for a user-approved scope exclusion, or the approval object for a
corrected target.  Those bounded transformations change the role digest even
though the reviewed role did not change.

This module builds a non-accepting bridge from an exact private map, its exact
public projection, the selected accepted graph identity, and the accepted role
digests.  It never treats an envelope's own content hash as authority.  The
private release guard must authenticate issuance, and a public caller must
supply envelope bytes obtained from its independently authenticated canonical
Git tree.
"""

from __future__ import annotations

import hashlib
import json
import re
from collections.abc import Iterable, Mapping, Sequence
from typing import Any

try:
    from scripts.corrected_target_identity import (
        CORRECTED_TARGET_RECORD_SHA256_FIELD,
        CORRECTED_TARGET_REVIEW_SHA256_FIELD,
    )
    from scripts.obligation_evidence_projection import _source_role_contract
    from scripts.portable_evidence_identity import portable_evidence_sha256
except ModuleNotFoundError:  # pragma: no cover - direct-script import support.
    from corrected_target_identity import (
        CORRECTED_TARGET_RECORD_SHA256_FIELD,
        CORRECTED_TARGET_REVIEW_SHA256_FIELD,
    )
    from obligation_evidence_projection import _source_role_contract
    from portable_evidence_identity import portable_evidence_sha256


PUBLIC_SOURCE_ROLE_PROJECTION_FILE = "audit/public_source_role_projection.json"
PUBLIC_SOURCE_ROLE_PROJECTION_SCHEMA = 1
PUBLIC_SOURCE_ROLE_PROJECTION_BINDING_SCHEMA = 1
# Keep these wire-format values local so the terminal reader does not import a
# release CLI or display renderer. Focused parity tests pin them to the owner
# modules used by the private release guard.
PUBLIC_SOURCE_DISPLAY_PROJECTION_FIELD = "publication_source_display_projection"
PUBLIC_SOURCE_DISPLAY_PROJECTION_SCHEMA = 1
PUBLIC_SOURCE_DISPLAY_PROJECTION_MANIFEST = "audit/public_source_display_projection.json"
PUBLIC_SOURCE_DISPLAY_PROJECTION_GENERATOR = (
    "python3 scripts/public_source_display_projection.py"
)
PUBLIC_CORRECTED_TARGET_PROJECTION_FIELD = "publication_corrected_target_projection"
PUBLIC_SOURCE_ROLE_PROJECTION_CONTRACT = {
    "schema": 1,
    "private_role_identity": "accepted_source_role_contract_sha256",
    "public_role_identity": "all_public_visible_source_role_fields_v1",
    "public_map_projection": "scripts.public_release_projection.project_bytes",
    "allowed_withheld_field_paths": [
        "corrected_target.approval",
        "corrected_target.archival_source_locator",
        "user_approved_scope_exclusion.approval_reference",
        "user_approved_scope_exclusion.source_evidence",
        "user_approved_scope_exclusion.source_locator",
    ],
    "rule": (
        "The exact public map is the deterministic marker-bearing projection of "
        "the exact private map. Every accepted private role digest must match the "
        "private item. The public digest covers every retained public role field."
    ),
}
PUBLIC_SOURCE_ROLE_PROJECTION_CONTRACT_SHA256 = portable_evidence_sha256(
    PUBLIC_SOURCE_ROLE_PROJECTION_CONTRACT
)

_SHA256_RE = re.compile(r"^[0-9a-f]{64}$")
_PAPER_RE = re.compile(r"^[A-Za-z0-9][A-Za-z0-9_-]*$")
_ROLE_FIELDS = (
    "source_kind",
    "claim_bearing",
    "coverage_status",
    "inventory_role",
    "protocol_role",
    "source_scope_classification",
    "user_approved_scope_exclusion",
    "scope_disposition",
)
_SCOPE_REDACTION_FIELDS = frozenset(
    {"approval_reference", "source_evidence", "source_locator"}
)


class PublicSourceRoleProjectionError(ValueError):
    """A source-role bridge is malformed, stale, or unauthenticated."""


def accepted_source_role_sha256s_by_source_item(
    accepted_graph: object,
    paper_index: object,
) -> dict[str, str]:
    """Project unique accepted role digests from validated graph/index objects."""

    leaves = getattr(accepted_graph, "leaves", None)
    routes = getattr(paper_index, "route_leaf_sha256s_by_source_item", None)
    if not isinstance(leaves, Mapping) or not isinstance(routes, Mapping):
        raise PublicSourceRoleProjectionError(
            "accepted graph and paper index do not expose source-route material"
        )
    result: dict[str, str] = {}
    for raw_item_id, raw_roles in routes.items():
        item_id = str(raw_item_id or "").strip()
        if not item_id or not isinstance(raw_roles, Mapping):
            raise PublicSourceRoleProjectionError("accepted source route is malformed")
        atom_digests = raw_roles.get("source_atom")
        if not isinstance(atom_digests, Sequence) or isinstance(
            atom_digests, (str, bytes)
        ) or not atom_digests:
            raise PublicSourceRoleProjectionError(
                f"accepted source item {item_id!r} has no source atoms"
            )
        role_digests: set[str] = set()
        for leaf_digest in atom_digests:
            leaf = leaves.get(str(leaf_digest))
            payload = getattr(leaf, "semantic_payload", None)
            if not isinstance(payload, Mapping):
                raise PublicSourceRoleProjectionError(
                    f"accepted source item {item_id!r} names a missing source atom"
                )
            role_digests.add(
                _sha256(
                    payload.get("source_role_contract_sha256"),
                    f"accepted source item {item_id!r} role",
                )
            )
        if len(role_digests) != 1:
            raise PublicSourceRoleProjectionError(
                f"accepted source item {item_id!r} has inconsistent role digests"
            )
        result[item_id] = next(iter(role_digests))
    if not result:
        raise PublicSourceRoleProjectionError("accepted graph has no source routes")
    return result


def _sha256_bytes(value: bytes) -> str:
    return hashlib.sha256(value).hexdigest()


def _sha256(value: object, label: str) -> str:
    digest = str(value or "").strip().lower()
    if not _SHA256_RE.fullmatch(digest):
        raise PublicSourceRoleProjectionError(f"{label} must be a lowercase SHA-256")
    return digest


def _paper(value: object) -> str:
    paper = str(value or "").strip()
    if not _PAPER_RE.fullmatch(paper):
        raise PublicSourceRoleProjectionError("paper must be one canonical paper ID")
    return paper


def _json_object(raw: bytes, label: str) -> dict[str, Any]:
    if not isinstance(raw, bytes):
        raise PublicSourceRoleProjectionError(f"{label} bytes are required")
    try:
        value = json.loads(raw.decode("utf-8"))
    except (UnicodeDecodeError, json.JSONDecodeError) as exc:
        raise PublicSourceRoleProjectionError(f"{label} is not valid UTF-8 JSON: {exc}") from exc
    if not isinstance(value, dict):
        raise PublicSourceRoleProjectionError(f"{label} must be a JSON object")
    return value


def _material_sha256(label: str, value: Mapping[str, Any]) -> str:
    return portable_evidence_sha256({"schema": 1, label: value})


def _items(source_map: Mapping[str, Any], *, label: str) -> Mapping[str, Any]:
    items = source_map.get("items")
    if not isinstance(items, Mapping):
        raise PublicSourceRoleProjectionError(f"{label} items must be an object")
    if any(not isinstance(key, str) or not key for key in items):
        raise PublicSourceRoleProjectionError(f"{label} has an invalid source-item ID")
    return items


def _accepted_roles(
    values: Mapping[str, str | Iterable[str]],
) -> dict[str, str]:
    result: dict[str, str] = {}
    for raw_item_id, raw_value in values.items():
        if not isinstance(raw_item_id, str) or not raw_item_id:
            raise PublicSourceRoleProjectionError(
                "accepted source-role map has an invalid source-item ID"
            )
        candidates: list[object]
        if isinstance(raw_value, str):
            candidates = [raw_value]
        elif isinstance(raw_value, Iterable):
            candidates = list(raw_value)
        else:
            raise PublicSourceRoleProjectionError(
                f"accepted source item {raw_item_id!r} has no role digest"
            )
        digests = {
            _sha256(value, f"accepted source item {raw_item_id!r} role")
            for value in candidates
        }
        if len(digests) != 1:
            raise PublicSourceRoleProjectionError(
                f"accepted source item {raw_item_id!r} does not have one role digest"
            )
        result[raw_item_id] = next(iter(digests))
    if not result:
        raise PublicSourceRoleProjectionError("accepted source-role map is empty")
    return result


def _role_projection(item: Mapping[str, Any], *, public: bool) -> dict[str, Any]:
    projection = {field: item[field] for field in _ROLE_FIELDS if field in item}
    target = item.get("corrected_target")
    if target is None:
        return projection
    if not isinstance(target, Mapping):
        raise PublicSourceRoleProjectionError("corrected_target must be an object")
    if not public:
        # The canonical private projector performs the complete private schema
        # validation. This branch exists only for typed difference inspection.
        projection["corrected_target"] = dict(target)
        return projection
    if "approval" in target:
        raise PublicSourceRoleProjectionError(
            "public corrected_target retains private approval material"
        )
    _sha256(
        target.get(CORRECTED_TARGET_RECORD_SHA256_FIELD),
        f"public corrected_target {CORRECTED_TARGET_RECORD_SHA256_FIELD}",
    )
    _sha256(
        target.get(CORRECTED_TARGET_REVIEW_SHA256_FIELD),
        f"public corrected_target {CORRECTED_TARGET_REVIEW_SHA256_FIELD}",
    )
    # Cover the complete retained corrected-target object, not merely the
    # mathematical statement, so status/basis/defect metadata cannot drift.
    projection["corrected_target_public_projection"] = dict(target)
    return projection


def public_source_role_projection_sha256(item: Mapping[str, Any]) -> str:
    """Hash every role field retained in one public source-map item."""

    if not isinstance(item, Mapping):
        raise PublicSourceRoleProjectionError("public source item must be an object")
    if item.get("corrected_target") is None:
        try:
            return _source_role_contract(item)
        except Exception as exc:
            raise PublicSourceRoleProjectionError(str(exc)) from exc
    return portable_evidence_sha256(
        {"schema": 1, "public_source_role": _role_projection(item, public=True)}
    )


def _changed_scope_paths(
    private_item: Mapping[str, Any], public_item: Mapping[str, Any]
) -> list[str]:
    private_scope = private_item.get("user_approved_scope_exclusion")
    public_scope = public_item.get("user_approved_scope_exclusion")
    if private_scope == public_scope:
        return []
    if not isinstance(private_scope, Mapping) or not isinstance(public_scope, Mapping):
        raise PublicSourceRoleProjectionError(
            "projected user_approved_scope_exclusion is not an object"
        )
    if set(private_scope) != set(public_scope):
        raise PublicSourceRoleProjectionError(
            "public projection changed scope-exclusion fields"
        )
    changed = {
        key for key in private_scope if private_scope.get(key) != public_scope.get(key)
    }
    if not changed or not changed.issubset(_SCOPE_REDACTION_FIELDS):
        raise PublicSourceRoleProjectionError(
            "public projection changed a non-withheld scope-exclusion field"
        )
    return [f"user_approved_scope_exclusion.{key}" for key in sorted(changed)]


def _withheld_field_paths(
    private_item: Mapping[str, Any], public_item: Mapping[str, Any]
) -> tuple[str, ...]:
    paths = _changed_scope_paths(private_item, public_item)
    private_target = private_item.get("corrected_target")
    public_target = public_item.get("corrected_target")
    if private_target is None and public_target is None:
        return tuple(paths)
    if not isinstance(private_target, Mapping) or not isinstance(public_target, Mapping):
        raise PublicSourceRoleProjectionError(
            "private and public corrected_target records must both be objects"
        )
    if "approval" not in private_target or "approval" in public_target:
        raise PublicSourceRoleProjectionError(
            "corrected-target projection has the wrong approval boundary"
        )
    expected_public_target = {
        key: value for key, value in private_target.items() if key != "approval"
    }
    if set(public_target) != set(expected_public_target):
        raise PublicSourceRoleProjectionError(
            "public corrected_target changed retained fields"
        )
    changed_target_fields = {
        key
        for key in expected_public_target
        if public_target.get(key) != expected_public_target.get(key)
    }
    if not changed_target_fields.issubset({"archival_source_locator"}):
        raise PublicSourceRoleProjectionError(
            "public corrected_target changed a non-withheld retained field"
        )
    if "archival_source_locator" in changed_target_fields:
        paths.append("corrected_target.archival_source_locator")
    paths.append("corrected_target.approval")
    return tuple(sorted(paths))


def _validate_public_map_and_display(
    *,
    paper: str,
    public_source_map: Mapping[str, Any],
    public_source_map_bytes: bytes,
    public_display_manifest: Mapping[str, Any],
    public_display_manifest_bytes: bytes,
    private_source_map_bytes: bytes | None,
) -> None:
    if public_source_map.get("paper") != paper:
        raise PublicSourceRoleProjectionError("public source map belongs to another paper")
    marker = public_source_map.get(PUBLIC_SOURCE_DISPLAY_PROJECTION_FIELD)
    expected_marker = {
        "schema": PUBLIC_SOURCE_DISPLAY_PROJECTION_SCHEMA,
        "manifest": PUBLIC_SOURCE_DISPLAY_PROJECTION_MANIFEST,
        "raw_source_bytes_included": False,
    }
    if marker != expected_marker:
        raise PublicSourceRoleProjectionError(
            "public source map lacks the exact display-projection marker"
        )
    if public_source_map.get(PUBLIC_CORRECTED_TARGET_PROJECTION_FIELD) not in (
        None,
        {"schema": 1, "approval_material_included": False},
    ):
        raise PublicSourceRoleProjectionError(
            "public corrected-target projection marker is malformed"
        )
    expected_path = f"papers/{paper}/{PUBLIC_SOURCE_DISPLAY_PROJECTION_MANIFEST}"
    checks = {
        "schema": PUBLIC_SOURCE_DISPLAY_PROJECTION_SCHEMA,
        "generator": PUBLIC_SOURCE_DISPLAY_PROJECTION_GENERATOR,
        "paper_id": paper,
        "public_manifest_path": expected_path,
        "public_source_map_sha256": _sha256_bytes(public_source_map_bytes),
    }
    for field, expected in checks.items():
        if public_display_manifest.get(field) != expected:
            raise PublicSourceRoleProjectionError(
                f"public display manifest {field} does not match current public material"
            )
    if private_source_map_bytes is not None and public_display_manifest.get(
        "private_source_map_sha256"
    ) != _sha256_bytes(private_source_map_bytes):
        raise PublicSourceRoleProjectionError(
            "public display manifest private_source_map_sha256 does not match private map"
        )
    if public_display_manifest.get("raw_source_artifact_included") is not False:
        raise PublicSourceRoleProjectionError(
            "public display manifest does not declare raw_source_artifact_included=false"
        )
    # The bytes argument is intentional: callers authenticate and pin the exact
    # committed manifest blob, while the material digest below also makes the
    # parsed-object convention explicit.
    if not public_display_manifest_bytes:
        raise PublicSourceRoleProjectionError("public display manifest bytes are empty")


def build_public_source_role_projection_envelope(
    *,
    paper: str,
    private_source_map_bytes: bytes,
    public_source_map_bytes: bytes,
    public_display_manifest_bytes: bytes,
    accepted_graph_sha256: str,
    accepted_role_sha256s_by_source_item: Mapping[str, str | Iterable[str]],
) -> dict[str, Any]:
    """Build one guard-issued bridge from exact private and public material."""

    paper = _paper(paper)
    graph_sha256 = _sha256(accepted_graph_sha256, "accepted graph")
    private_map = _json_object(private_source_map_bytes, "private source map")
    public_map = _json_object(public_source_map_bytes, "public source map")
    display = _json_object(public_display_manifest_bytes, "public display manifest")
    if private_map.get("paper") != paper:
        raise PublicSourceRoleProjectionError("private source map belongs to another paper")
    expected_path = f"papers/{paper}/audit/paper_statement_map.json"
    try:
        try:
            from scripts.public_release_projection import project_bytes
        except ModuleNotFoundError:  # pragma: no cover - direct-script support.
            from public_release_projection import project_bytes
        expected_public_bytes = project_bytes(
            expected_path,
            private_source_map_bytes,
            include_source_display_marker=True,
        )
    except Exception as exc:
        raise PublicSourceRoleProjectionError(
            f"cannot construct canonical public source-map projection: {exc}"
        ) from exc
    if public_source_map_bytes != expected_public_bytes:
        raise PublicSourceRoleProjectionError(
            "public source map is not the exact canonical marker-bearing private projection"
        )
    _validate_public_map_and_display(
        paper=paper,
        public_source_map=public_map,
        public_source_map_bytes=public_source_map_bytes,
        public_display_manifest=display,
        public_display_manifest_bytes=public_display_manifest_bytes,
        private_source_map_bytes=private_source_map_bytes,
    )
    accepted_roles = _accepted_roles(accepted_role_sha256s_by_source_item)
    private_items = _items(private_map, label="private source map")
    public_items = _items(public_map, label="public source map")
    bindings: dict[str, dict[str, Any]] = {}
    for item_id, accepted_role in sorted(accepted_roles.items()):
        private_item = private_items.get(item_id)
        public_item = public_items.get(item_id)
        if not isinstance(private_item, Mapping) or not isinstance(public_item, Mapping):
            raise PublicSourceRoleProjectionError(
                f"accepted source item {item_id!r} is absent from a source map"
            )
        try:
            private_role = _source_role_contract(private_item)
        except Exception as exc:
            raise PublicSourceRoleProjectionError(str(exc)) from exc
        if private_role != accepted_role:
            raise PublicSourceRoleProjectionError(
                f"private source item {item_id!r} does not match its accepted role digest"
            )
        public_role = public_source_role_projection_sha256(public_item)
        paths = _withheld_field_paths(private_item, public_item)
        if public_role != accepted_role and not paths:
            raise PublicSourceRoleProjectionError(
                f"public source item {item_id!r} changed role without an allowed withholding"
            )
        bindings[item_id] = {
            "accepted_source_role_contract_sha256": accepted_role,
            "public_source_role_projection_sha256": public_role,
            "schema": PUBLIC_SOURCE_ROLE_PROJECTION_BINDING_SCHEMA,
            "withheld_field_paths": list(paths),
        }
    return {
        "acceptance_credential": False,
        "accepted_graph_sha256": graph_sha256,
        "bindings_by_source_item": bindings,
        "paper": paper,
        "private_role_material_included": False,
        "private_source_map_material_sha256": _material_sha256(
            "private_source_map", private_map
        ),
        "private_source_map_sha256": _sha256_bytes(private_source_map_bytes),
        "projection_contract_sha256": PUBLIC_SOURCE_ROLE_PROJECTION_CONTRACT_SHA256,
        "public_display_manifest_material_sha256": _material_sha256(
            "public_display_manifest", display
        ),
        "public_display_manifest_sha256": _sha256_bytes(public_display_manifest_bytes),
        "public_source_map_material_sha256": _material_sha256(
            "public_source_map", public_map
        ),
        "public_source_map_sha256": _sha256_bytes(public_source_map_bytes),
        "raw_private_approval_material_included": False,
        "schema": PUBLIC_SOURCE_ROLE_PROJECTION_SCHEMA,
    }


def canonical_public_source_role_projection_bytes(envelope: Mapping[str, Any]) -> bytes:
    """Serialize one envelope canonically; its bytes are not self-authority."""

    try:
        return (
            json.dumps(
                envelope,
                ensure_ascii=False,
                indent=2,
                sort_keys=True,
                allow_nan=False,
            )
            + "\n"
        ).encode("utf-8")
    except (TypeError, ValueError) as exc:
        raise PublicSourceRoleProjectionError(
            "public source-role projection is not canonical JSON"
        ) from exc


def validate_public_source_role_projection_envelope(
    envelope_bytes: bytes,
    *,
    paper: str,
    private_source_map_bytes: bytes,
    public_source_map_bytes: bytes,
    public_display_manifest_bytes: bytes,
    accepted_graph_sha256: str,
    accepted_role_sha256s_by_source_item: Mapping[str, str | Iterable[str]],
) -> dict[str, Any]:
    """Require canonical bytes for a freshly guard-derived envelope."""

    expected = build_public_source_role_projection_envelope(
        paper=paper,
        private_source_map_bytes=private_source_map_bytes,
        public_source_map_bytes=public_source_map_bytes,
        public_display_manifest_bytes=public_display_manifest_bytes,
        accepted_graph_sha256=accepted_graph_sha256,
        accepted_role_sha256s_by_source_item=accepted_role_sha256s_by_source_item,
    )
    actual = _json_object(envelope_bytes, "public source-role projection")
    if actual != expected or envelope_bytes != canonical_public_source_role_projection_bytes(
        expected
    ):
        raise PublicSourceRoleProjectionError(
            "public source-role projection does not match authenticated private inputs"
        )
    return expected


def validate_runtime_public_source_role_projection(
    *,
    trusted_envelope_bytes: bytes,
    paper: str,
    public_source_map_bytes: bytes,
    public_display_manifest_bytes: bytes,
    accepted_graph_sha256: str,
    accepted_role_sha256s_by_source_item: Mapping[str, str | Iterable[str]],
) -> dict[str, str]:
    """Validate a bridge already authenticated by canonical public Git.

    This function does not decide whether bytes are trusted. A caller must read
    ``trusted_envelope_bytes`` from the authenticated canonical Git object, and
    separately require the working-tree envelope to be byte-identical to it.
    """

    paper = _paper(paper)
    graph_sha256 = _sha256(accepted_graph_sha256, "accepted graph")
    envelope = _json_object(trusted_envelope_bytes, "trusted source-role envelope")
    if trusted_envelope_bytes != canonical_public_source_role_projection_bytes(envelope):
        raise PublicSourceRoleProjectionError(
            "trusted source-role envelope is not the canonical serialization"
        )
    public_map = _json_object(public_source_map_bytes, "public source map")
    display = _json_object(public_display_manifest_bytes, "public display manifest")
    expected_top_fields = {
        "acceptance_credential",
        "accepted_graph_sha256",
        "bindings_by_source_item",
        "paper",
        "private_role_material_included",
        "private_source_map_material_sha256",
        "private_source_map_sha256",
        "projection_contract_sha256",
        "public_display_manifest_material_sha256",
        "public_display_manifest_sha256",
        "public_source_map_material_sha256",
        "public_source_map_sha256",
        "raw_private_approval_material_included",
        "schema",
    }
    if set(envelope) != expected_top_fields:
        raise PublicSourceRoleProjectionError("trusted source-role envelope fields are malformed")
    if (
        envelope.get("schema") != PUBLIC_SOURCE_ROLE_PROJECTION_SCHEMA
        or envelope.get("acceptance_credential") is not False
        or envelope.get("paper") != paper
        or envelope.get("accepted_graph_sha256") != graph_sha256
        or envelope.get("projection_contract_sha256")
        != PUBLIC_SOURCE_ROLE_PROJECTION_CONTRACT_SHA256
        or envelope.get("private_role_material_included") is not False
        or envelope.get("raw_private_approval_material_included") is not False
    ):
        raise PublicSourceRoleProjectionError(
            "trusted source-role envelope authority or paper identity is stale"
        )
    for field in (
        "private_source_map_material_sha256",
        "private_source_map_sha256",
        "public_display_manifest_material_sha256",
        "public_display_manifest_sha256",
        "public_source_map_material_sha256",
        "public_source_map_sha256",
    ):
        _sha256(envelope.get(field), f"trusted source-role envelope {field}")
    expected_hashes = {
        "public_source_map_sha256": _sha256_bytes(public_source_map_bytes),
        "public_source_map_material_sha256": _material_sha256(
            "public_source_map", public_map
        ),
        "public_display_manifest_sha256": _sha256_bytes(public_display_manifest_bytes),
        "public_display_manifest_material_sha256": _material_sha256(
            "public_display_manifest", display
        ),
    }
    for field, expected in expected_hashes.items():
        if envelope.get(field) != expected:
            raise PublicSourceRoleProjectionError(
                f"trusted source-role envelope {field} does not match current public material"
            )
    _validate_public_map_and_display(
        paper=paper,
        public_source_map=public_map,
        public_source_map_bytes=public_source_map_bytes,
        public_display_manifest=display,
        public_display_manifest_bytes=public_display_manifest_bytes,
        private_source_map_bytes=None,
    )
    accepted_roles = _accepted_roles(accepted_role_sha256s_by_source_item)
    public_items = _items(public_map, label="public source map")
    bindings = envelope.get("bindings_by_source_item")
    if not isinstance(bindings, Mapping) or set(bindings) != set(accepted_roles):
        raise PublicSourceRoleProjectionError(
            "trusted source-role envelope does not cover the exact accepted source routes"
        )
    result: dict[str, str] = {}
    for item_id, accepted_role in sorted(accepted_roles.items()):
        binding = bindings.get(item_id)
        item = public_items.get(item_id)
        if not isinstance(binding, Mapping) or not isinstance(item, Mapping):
            raise PublicSourceRoleProjectionError(
                f"trusted source-role binding {item_id!r} is malformed"
            )
        expected_binding_fields = {
            "accepted_source_role_contract_sha256",
            "public_source_role_projection_sha256",
            "schema",
            "withheld_field_paths",
        }
        paths = binding.get("withheld_field_paths")
        if (
            set(binding) != expected_binding_fields
            or binding.get("schema") != PUBLIC_SOURCE_ROLE_PROJECTION_BINDING_SCHEMA
            or binding.get("accepted_source_role_contract_sha256") != accepted_role
            or not isinstance(paths, list)
            or paths != sorted(set(paths))
            or any(
                path not in PUBLIC_SOURCE_ROLE_PROJECTION_CONTRACT[
                    "allowed_withheld_field_paths"
                ]
                for path in paths
            )
        ):
            raise PublicSourceRoleProjectionError(
                f"trusted source-role binding {item_id!r} is stale or malformed"
            )
        current_public_role = public_source_role_projection_sha256(item)
        if binding.get("public_source_role_projection_sha256") != current_public_role:
            raise PublicSourceRoleProjectionError(
                f"public source item {item_id!r} does not match its trusted projected role"
            )
        if current_public_role != accepted_role and not paths:
            raise PublicSourceRoleProjectionError(
                f"public source item {item_id!r} changed role without an authenticated withholding"
            )
        result[item_id] = current_public_role
    return result


def public_source_role_projection_envelope_sha256(envelope: Mapping[str, Any]) -> str:
    """Return an external registry key; never accept it from the envelope itself."""

    return portable_evidence_sha256(
        {"schema": 1, "public_source_role_projection": dict(envelope)}
    )
