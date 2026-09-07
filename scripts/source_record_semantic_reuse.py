#!/usr/bin/env python3
"""Validate canonical raw receipts by current declaration semantics.

Whole-file hashes are useful fast paths and archival provenance, but they are
not mathematical identities.  This module is the normal fallback when a saved
Lean import closure has different repository-source bytes.  It asks Lean to
elaborate each receipt-bound qualified declaration in the current checkout and
compares the current elaborated signature, proposition graph, and transitive
semantic dependency identity with the canonical receipt.  The historical
loaded-module closure remains lookup provenance; it is not reinterpreted as a
mathematical validity condition.

The issuing engine version is deliberately absent.  Every current verifier
checks every supported canonical receipt directly; there is no pairwise engine
compatibility graph.
"""

from __future__ import annotations

import hashlib
import json
import os
import re
import tempfile
from pathlib import Path
from typing import Any, Mapping

try:
    from scripts.authenticated_manifest_store import (
        configured_review_row_proposition_graph_sha256,
        elaborated_proposition_graph_sha256,
        validated_authenticated_manifest_store_entries,
    )
    from scripts.lean_signature_manifest import (
        run_lean_signature_manifests,
        semantic_dependency_manifest,
        signature_manifest_digest,
    )
    from scripts.source_record_producer_provenance import (
        fingerprint_without_raw_producer_provenance,
    )
    from scripts.source_record_legacy_contract import (
        SOURCE_RECORD_SEMANTIC_REUSE_POLICY as POLICY,
        SOURCE_RECORD_SEMANTIC_VALIDATION_BASENAME as AUTHORITY_FILENAME,
    )
    from scripts.semantic_reuse_authority import CurrentSemanticReuseAuthority
except ModuleNotFoundError:  # pragma: no cover - direct-script import path.
    from authenticated_manifest_store import (  # type: ignore
        configured_review_row_proposition_graph_sha256,
        elaborated_proposition_graph_sha256,
        validated_authenticated_manifest_store_entries,
    )
    from lean_signature_manifest import (  # type: ignore
        run_lean_signature_manifests,
        semantic_dependency_manifest,
        signature_manifest_digest,
    )
    from source_record_producer_provenance import (  # type: ignore
        fingerprint_without_raw_producer_provenance,
    )
    from source_record_legacy_contract import (  # type: ignore
        SOURCE_RECORD_SEMANTIC_REUSE_POLICY as POLICY,
        SOURCE_RECORD_SEMANTIC_VALIDATION_BASENAME as AUTHORITY_FILENAME,
    )
    from semantic_reuse_authority import CurrentSemanticReuseAuthority  # type: ignore


SCHEMA = 1
CACHE_SCHEMA = 1
CACHE_FILENAME = "source_record_semantic_reuse.json"
AUTHORITY_SCHEMA = 1
AUTHORITY_ROLE = "current_declaration_semantic_validation"
_SHA256_RE = re.compile(r"^[0-9a-f]{64}$")
_SEPARATELY_REVALIDATED_FINGERPRINT_FIELDS = frozenset(
    {
        # The current verifier below checks these coordinates structurally:
        # exact configured roots, current per-paper semantic-model dimensions,
        # and proof-fidelity defects routed to their dedicated defect lane.
        # Source-to-Spec and paper-coverage gates own the current map itself.
        "paper_statement_map_semantic_sha256",
        "relevant_status_sha256",
        "source_proof_fidelity_sha256",
        # Lean container coordinates are replaced by the declaration-level
        # signature/dependency/graph comparison below.
        "review_interface_source",
        "review_assumption_source",
        "lean_dependency_identities",
        "lean_import_closure_sha256",
    }
)


def _sha256(value: object) -> str:
    text = str(value or "").strip().lower()
    return text if _SHA256_RE.fullmatch(text) else ""


def _canonical_sha256(value: object) -> str:
    try:
        encoded = json.dumps(
            value, sort_keys=True, separators=(",", ":"), ensure_ascii=True
        ).encode("utf-8")
    except (TypeError, ValueError):
        return ""
    return hashlib.sha256(encoded).hexdigest()


def semantic_reuse_cache_path(paper_dir: Path) -> Path:
    """Return the ignored operational cache path for one paper."""

    return paper_dir / ".review_traces" / CACHE_FILENAME


def semantic_validation_authority_path(paper_dir: Path) -> Path:
    """Return the tracked machine semantic-validation receipt path."""

    return paper_dir / "audit" / AUTHORITY_FILENAME


def _semantic_validation_authority_payload(
    *,
    paper: str,
    raw_audit_file_sha256: str,
    material: Mapping[str, Any],
    result: Mapping[str, Any],
) -> dict[str, Any]:
    payload: dict[str, Any] = {
        "schema": AUTHORITY_SCHEMA,
        "evidence_role": AUTHORITY_ROLE,
        "acceptance_credential": True,
        "paper": paper,
        "policy": POLICY,
        "raw_audit_file_sha256": raw_audit_file_sha256,
        "watched_repository_material": dict(material),
        "watched_repository_material_sha256": _canonical_sha256(material),
        "result": dict(result),
    }
    payload["semantic_validation_receipt_sha256"] = _canonical_sha256(payload)
    return payload


def _write_json_atomic(path: Path, payload: Mapping[str, Any]) -> str:
    """Write one deterministic machine receipt through an atomic rename."""

    try:
        path.parent.mkdir(parents=True, exist_ok=True)
        encoded = json.dumps(payload, indent=2, sort_keys=True) + "\n"
        with tempfile.NamedTemporaryFile(
            mode="w",
            encoding="utf-8",
            dir=path.parent,
            prefix=path.name + ".",
            suffix=".tmp",
            delete=False,
        ) as stream:
            stream.write(encoded)
            stream.flush()
            os.fsync(stream.fileno())
            temporary = Path(stream.name)
        os.replace(temporary, path)
    except OSError as exc:
        try:
            temporary.unlink(missing_ok=True)
        except (OSError, UnboundLocalError):
            pass
        return f"could not write semantic-validation receipt: {exc}"
    return ""


def _repository_material_snapshot(
    root: Path, paths: set[Path]
) -> tuple[dict[str, dict[str, str]], str]:
    """Hash an exact repository-relative input set for cache reuse only."""

    root = root.resolve()
    snapshot: dict[str, dict[str, str]] = {}
    for path in sorted({candidate.resolve() for candidate in paths}, key=str):
        try:
            relative = path.relative_to(root).as_posix()
        except ValueError:
            return {}, "semantic-reuse cache input escapes the repository"
        try:
            content = path.read_bytes()
        except FileNotFoundError:
            snapshot[relative] = {"state": "missing", "sha256": ""}
        except OSError as exc:
            return {}, f"semantic-reuse cache input is unreadable: {relative}: {exc}"
        else:
            snapshot[relative] = {
                "state": "present",
                "sha256": hashlib.sha256(content).hexdigest(),
            }
    return snapshot, ""


def _semantic_authority_material(
    material: Mapping[str, Any],
    paper_dir: Path,
    *,
    drop_statement_map: bool = False,
) -> dict[str, Any]:
    """Exclude separately validated derived inputs from semantic identity.

    The completed Lean pass validates every manifest identity against the raw
    configured rows.  The tracked manifest authority is then free to rebind
    those same manifests to a current compiled cache context; hashing that
    derived index here would make successful cache publication invalidate the
    semantic result that authorized it.  Acceptance-facing authority also
    excludes the paper statement map: current source coverage, source-to-Spec,
    and Spec/proof gates own that map, while this receipt owns only the Lean
    meaning of the configured raw-review declarations.  Operational cache
    reads retain the map's exact bytes for the cheapest scheduling fast path.
    """

    try:
        audit_dir = paper_dir.resolve() / "audit"
        root = paper_dir.resolve().parents[1]
        excluded = {
            (audit_dir / "lean_signature_manifest_cache_authority.json")
            .relative_to(root)
            .as_posix()
        }
        if drop_statement_map:
            excluded.add(
                (audit_dir / "paper_statement_map.json")
                .relative_to(root)
                .as_posix()
            )
    except (IndexError, OSError, ValueError):
        return dict(material)
    return {
        str(relative): raw
        for relative, raw in material.items()
        if str(relative) not in excluded
    }


def _semantic_identity_from_rows(
    raw_audit: Mapping[str, Any],
) -> tuple[tuple[str, ...], str]:
    """Reconstruct the canonical declaration identity stored by Lean.

    The digest intentionally excludes declaration locations, source-container
    hashes, producer versions, and engine implementation files.  Each row is
    nevertheless bound to its elaborated signature, proposition graph, and
    transitive semantic dependency digest.
    """

    rows, row_error = _validated_raw_rows(raw_audit)
    if row_error:
        return (), ""
    reviewed = tuple(sorted(rows))
    identity = {
        "reviewed_declarations": [
            {
                "qualified_declaration": qualified,
                "elaborated_signature_sha256": _sha256(
                    rows[qualified].get("elaborated_signature_sha256")
                ),
                "semantic_dependency_sha256": _sha256(
                    rows[qualified].get("semantic_dependency_sha256")
                ),
                "elaborated_proposition_graph_sha256": (
                    configured_review_row_proposition_graph_sha256(rows[qualified])
                ),
            }
            for qualified in reviewed
        ]
    }
    return reviewed, _canonical_sha256(identity)


def _validated_cache_result(
    value: object,
    paper: str,
    *,
    raw_audit: Mapping[str, Any] | None = None,
) -> dict[str, Any] | None:
    """Validate the non-accepting cached fast-identity result shape."""

    if not isinstance(value, Mapping):
        return None
    semantic = value.get("semantic_receipt_reuse")
    if not (
        value.get("schema") == 1
        and value.get("paper") == paper
        and value.get("current") is True
        and value.get("external_artifacts_revalidated") is False
        and isinstance(semantic, Mapping)
        and semantic.get("schema") == SCHEMA
        and semantic.get("policy") == POLICY
        and semantic.get("paper") == paper
        and semantic.get("current") is True
        and isinstance(semantic.get("reviewed_declaration_count"), int)
        and int(semantic["reviewed_declaration_count"]) > 0
        and _sha256(semantic.get("semantic_identity_sha256"))
    ):
        return None
    if raw_audit is not None:
        reviewed, semantic_identity = _semantic_identity_from_rows(raw_audit)
        if (
            not reviewed
            or semantic.get("reviewed_declaration_count") != len(reviewed)
            or _sha256(semantic.get("semantic_identity_sha256"))
            != semantic_identity
        ):
            return None
    return dict(value)


def write_semantic_reuse_cache(
    *,
    root: Path,
    paper_dir: Path,
    raw_audit_file_sha256: str,
    watched_paths: set[Path],
    result: Mapping[str, Any],
) -> str:
    """Persist one input-bound scheduling cache after current Lean validation.

    The cache is ignored, explicitly non-accepting, and never substitutes for
    the strict closeout transaction.  It only prevents the planner from
    relaunching the same repository-semantic check while every watched byte is
    unchanged.
    """

    if not _sha256(raw_audit_file_sha256):
        return "semantic-reuse cache lacks a valid raw-audit file digest"
    validated_result = _validated_cache_result(result, paper_dir.name)
    if validated_result is None:
        return "semantic-reuse cache result is malformed"
    material, material_error = _repository_material_snapshot(root, watched_paths)
    if material_error:
        return material_error
    payload = {
        "schema": CACHE_SCHEMA,
        "acceptance_credential": False,
        "operational_scheduling_only": True,
        "paper": paper_dir.name,
        "policy": POLICY,
        "raw_audit_file_sha256": raw_audit_file_sha256,
        "watched_repository_material": material,
        "watched_repository_material_sha256": _canonical_sha256(material),
        "result": validated_result,
    }
    cache_error = _write_json_atomic(semantic_reuse_cache_path(paper_dir), payload)
    if cache_error:
        return cache_error.replace(
            "semantic-validation receipt", "semantic-reuse cache"
        )
    authority = _semantic_validation_authority_payload(
        paper=paper_dir.name,
        raw_audit_file_sha256=raw_audit_file_sha256,
        material=material,
        result=validated_result,
    )
    return _write_json_atomic(
        semantic_validation_authority_path(paper_dir), authority
    )


def load_semantic_reuse_cache(
    *,
    root: Path,
    paper_dir: Path,
    raw_audit_file_sha256: str,
) -> dict[str, Any] | None:
    """Return an exact-input cache hit, never an acceptance credential."""

    try:
        payload = json.loads(
            semantic_reuse_cache_path(paper_dir).read_text(encoding="utf-8")
        )
    except (OSError, json.JSONDecodeError):
        return None
    if not isinstance(payload, Mapping):
        return None
    material = payload.get("watched_repository_material")
    if not (
        payload.get("schema") == CACHE_SCHEMA
        and payload.get("acceptance_credential") is False
        and payload.get("operational_scheduling_only") is True
        and payload.get("paper") == paper_dir.name
        and payload.get("policy") == POLICY
        and payload.get("raw_audit_file_sha256") == raw_audit_file_sha256
        and isinstance(material, Mapping)
        and payload.get("watched_repository_material_sha256")
        == _canonical_sha256(material)
    ):
        return None
    effective_material = _semantic_authority_material(material, paper_dir)
    watched_paths = {root / str(relative) for relative in effective_material}
    current_material, material_error = _repository_material_snapshot(
        root, watched_paths
    )
    if material_error or current_material != effective_material:
        return None
    return _validated_cache_result(payload.get("result"), paper_dir.name)


def load_current_semantic_reuse_authority(
    *,
    root: Path,
    paper_dir: Path,
    raw_audit_file_sha256: str,
    raw_audit: Mapping[str, Any],
    authority_raw_bytes: bytes | None = None,
) -> CurrentSemanticReuseAuthority | None:
    """Issue current semantic authority from an exact-input machine result.

    Unlike :func:`load_semantic_reuse_cache`, this is an acceptance-facing
    projection.  It revalidates the canonical declaration digest from the raw
    audit instead of trusting the cached summary and exposes the exact watched
    material so a closeout provider can enforce a start/end mutation boundary.
    """

    try:
        payload = json.loads(
            authority_raw_bytes.decode("utf-8")
            if authority_raw_bytes is not None
            else semantic_validation_authority_path(paper_dir).read_text(
                encoding="utf-8"
            )
        )
    except (OSError, UnicodeDecodeError, json.JSONDecodeError):
        return None
    if not isinstance(payload, Mapping):
        return None
    material = payload.get("watched_repository_material")
    if not (
        payload.get("schema") == AUTHORITY_SCHEMA
        and payload.get("evidence_role") == AUTHORITY_ROLE
        and payload.get("acceptance_credential") is True
        and payload.get("paper") == paper_dir.name
        and payload.get("policy") == POLICY
        and payload.get("raw_audit_file_sha256") == raw_audit_file_sha256
        and isinstance(material, Mapping)
        and payload.get("watched_repository_material_sha256")
        == _canonical_sha256(material)
        and _sha256(payload.get("semantic_validation_receipt_sha256"))
        == _canonical_sha256(
            {
                key: value
                for key, value in payload.items()
                if key != "semantic_validation_receipt_sha256"
            }
        )
    ):
        return None
    effective_material = _semantic_authority_material(
        material, paper_dir, drop_statement_map=True
    )
    current_material, material_error = _repository_material_snapshot(
        root, {root / str(relative) for relative in effective_material}
    )
    if material_error or current_material != effective_material:
        return None
    validated_result = _validated_cache_result(
        payload.get("result"), paper_dir.name, raw_audit=raw_audit
    )
    if validated_result is None:
        return None
    reviewed, semantic_identity = _semantic_identity_from_rows(raw_audit)
    normalized_material: list[tuple[str, str, str]] = []
    for relative, raw in sorted(effective_material.items()):
        if not isinstance(relative, str) or not isinstance(raw, Mapping):
            return None
        state = str(raw.get("state") or "")
        digest = str(raw.get("sha256") or "").strip().lower()
        if state not in {"present", "missing"}:
            return None
        if state == "present" and not _SHA256_RE.fullmatch(digest):
            return None
        if state == "missing" and digest:
            return None
        normalized_material.append((relative, state, digest))
    return CurrentSemanticReuseAuthority(
        paper=paper_dir.name,
        raw_audit_file_sha256=raw_audit_file_sha256,
        semantic_identity_sha256=semantic_identity,
        reviewed_declarations=reviewed,
        watched_repository_material=tuple(normalized_material),
        result=validated_result,
    )


def promote_semantic_reuse_cache_authority(
    *,
    root: Path,
    paper_dir: Path,
    raw_audit_file_sha256: str,
    raw_audit: Mapping[str, Any],
) -> str:
    """Promote an exact current scheduling result without rerunning Lean."""

    try:
        cache = json.loads(
            semantic_reuse_cache_path(paper_dir).read_text(encoding="utf-8")
        )
    except (OSError, json.JSONDecodeError) as exc:
        return f"semantic-reuse cache is unavailable: {exc}"
    if not isinstance(cache, Mapping):
        return "semantic-reuse cache is malformed"
    material = cache.get("watched_repository_material")
    if not (
        cache.get("schema") == CACHE_SCHEMA
        and cache.get("acceptance_credential") is False
        and cache.get("operational_scheduling_only") is True
        and cache.get("paper") == paper_dir.name
        and cache.get("policy") == POLICY
        and cache.get("raw_audit_file_sha256") == raw_audit_file_sha256
        and isinstance(material, Mapping)
        and cache.get("watched_repository_material_sha256")
        == _canonical_sha256(material)
    ):
        return "semantic-reuse cache is not bound to the current raw audit"
    effective_material = _semantic_authority_material(material, paper_dir)
    current_material, material_error = _repository_material_snapshot(
        root, {root / str(relative) for relative in effective_material}
    )
    if material_error or current_material != effective_material:
        return material_error or "semantic-reuse watched material changed"
    result = _validated_cache_result(
        cache.get("result"), paper_dir.name, raw_audit=raw_audit
    )
    if result is None:
        return "semantic-reuse cache does not match the canonical raw rows"
    authority = _semantic_validation_authority_payload(
        paper=paper_dir.name,
        raw_audit_file_sha256=raw_audit_file_sha256,
        material=effective_material,
        result=result,
    )
    return _write_json_atomic(
        semantic_validation_authority_path(paper_dir), authority
    )


def rebind_semantic_validation_authority_controls(
    *,
    root: Path,
    paper_dir: Path,
    raw_audit: Mapping[str, Any],
    current_status_control_sha256: str,
    current_status_file_sha256: str,
    current_source_proof_fidelity_sha256: str,
    current_source_proof_fidelity_file_sha256: str,
    source_proof_fidelity_path: Path | None,
) -> str:
    """Rebind presentation containers after their semantic controls are unchanged.

    A successful declaration-semantic pass historically watched ``status.json``
    byte-for-byte.  That made a report link, line count, or other presentation
    metadata invalidate the scheduling fast path even though the raw receipt
    already records a narrow digest of every status control consumed by the
    source-record generator.  An earlier writer also joined an already
    repository-relative fidelity-ledger path to the paper directory, recording
    a nonexistent doubled path.

    This transition performs no Lean work and grants no new mathematical
    credit.  It is available only when the caller has independently recomputed
    the exact status-control and source-proof-fidelity semantic digests and both
    equal the canonical raw receipt.  Every other authority input remains
    byte-exact.  The resulting authority watches the current status bytes and
    the correctly resolved fidelity ledger, so existing exact-input consumers
    can continue without a raw or semantic reissue.
    """

    root = root.resolve()
    paper_dir = paper_dir.resolve()
    fingerprint = raw_audit.get("source_record_input_fingerprint")
    if not isinstance(fingerprint, Mapping):
        return "canonical raw receipt has no source-record input fingerprint"
    recorded_status = _sha256(fingerprint.get("relevant_status_sha256"))
    recorded_fidelity = _sha256(
        fingerprint.get("source_proof_fidelity_sha256")
    )
    if (
        not recorded_status
        or recorded_status != _sha256(current_status_control_sha256)
    ):
        return "current status controls differ from the canonical raw receipt"
    if recorded_fidelity != _sha256(current_source_proof_fidelity_sha256):
        return "current source-proof fidelity semantics differ from the canonical raw receipt"

    raw_path = paper_dir / "audit" / "source_record_audit.json"
    try:
        raw_bytes = raw_path.read_bytes()
        exact_raw_audit = json.loads(raw_bytes)
        authority_path = semantic_validation_authority_path(paper_dir)
        payload = json.loads(authority_path.read_text(encoding="utf-8"))
    except (OSError, UnicodeDecodeError, json.JSONDecodeError) as exc:
        return f"semantic-validation authority is unavailable: {exc}"
    if exact_raw_audit != raw_audit:
        return "caller raw audit differs from the canonical raw receipt"
    if not isinstance(payload, Mapping):
        return "semantic-validation authority is malformed"
    material = payload.get("watched_repository_material")
    if not (
        payload.get("schema") == AUTHORITY_SCHEMA
        and payload.get("evidence_role") == AUTHORITY_ROLE
        and payload.get("acceptance_credential") is True
        and payload.get("paper") == paper_dir.name
        and payload.get("policy") == POLICY
        and payload.get("raw_audit_file_sha256")
        == hashlib.sha256(raw_bytes).hexdigest()
        and isinstance(material, Mapping)
        and payload.get("watched_repository_material_sha256")
        == _canonical_sha256(material)
        and _sha256(payload.get("semantic_validation_receipt_sha256"))
        == _canonical_sha256(
            {
                key: value
                for key, value in payload.items()
                if key != "semantic_validation_receipt_sha256"
            }
        )
    ):
        return "semantic-validation authority receipt is invalid"
    result = _validated_cache_result(
        payload.get("result"), paper_dir.name, raw_audit=raw_audit
    )
    if result is None:
        return "semantic-validation authority does not match the canonical raw rows"

    try:
        status_relative = (paper_dir / "status.json").relative_to(root).as_posix()
        if source_proof_fidelity_path is not None:
            source_proof_fidelity_path.resolve().relative_to(root)
    except (OSError, ValueError):
        return "semantic-control path escapes the repository"

    # The statement map and generated manifest index have their own mandatory
    # validators.  Preserve the authority loader's existing exclusion policy,
    # then additionally replace only the two independently verified control
    # containers handled by this transition.
    comparable = _semantic_authority_material(
        material, paper_dir, drop_statement_map=True
    )
    comparable.pop(status_relative, None)
    for relative in tuple(comparable):
        if Path(relative).name == "source_proof_fidelity.json":
            comparable.pop(relative, None)
    current_comparable, material_error = _repository_material_snapshot(
        root, {root / str(relative) for relative in comparable}
    )
    if material_error:
        return material_error
    if current_comparable != comparable:
        return "semantic-validation authority has changed non-control inputs"

    rebound_material = dict(material)
    rebound_material.pop(status_relative, None)
    for relative in tuple(rebound_material):
        if Path(str(relative)).name == "source_proof_fidelity.json":
            rebound_material.pop(relative, None)
    rebound_paths = {paper_dir / "status.json"}
    if source_proof_fidelity_path is not None:
        rebound_paths.add(source_proof_fidelity_path)
    rebound_controls, material_error = _repository_material_snapshot(
        root, rebound_paths
    )
    if material_error:
        return material_error
    rebound_status = rebound_controls.get(status_relative)
    if not (
        isinstance(rebound_status, Mapping)
        and rebound_status.get("state") == "present"
        and rebound_status.get("sha256") == _sha256(current_status_file_sha256)
    ):
        return "status bytes changed while rebinding semantic controls"
    if source_proof_fidelity_path is not None:
        fidelity_relative = (
            source_proof_fidelity_path.resolve().relative_to(root).as_posix()
        )
        rebound_fidelity = rebound_controls.get(fidelity_relative)
        if not (
            isinstance(rebound_fidelity, Mapping)
            and rebound_fidelity.get("state") == "present"
            and rebound_fidelity.get("sha256")
            == _sha256(current_source_proof_fidelity_file_sha256)
        ):
            return "source-proof fidelity bytes changed while rebinding semantic controls"
    elif current_source_proof_fidelity_file_sha256:
        return "source-proof fidelity file digest was supplied without a ledger"
    rebound_material.update(rebound_controls)
    authority = _semantic_validation_authority_payload(
        paper=paper_dir.name,
        raw_audit_file_sha256=hashlib.sha256(raw_bytes).hexdigest(),
        material=rebound_material,
        result=result,
    )
    return _write_json_atomic(authority_path, authority)


def semantic_fingerprint_projection(value: object) -> dict[str, Any] | None:
    """Remove only byte-container/provenance coordinates from schema-10 input.

    Source artifacts, source-map semantics, status, proof-fidelity ledgers,
    protocol identities, toolchain controls, and every other obligation remain
    exact.  The removed Lean-file coordinates may be ignored only after the
    current semantic verifier below has accepted all receipt-bound roots.
    """

    projected = fingerprint_without_raw_producer_provenance(value)
    if not isinstance(projected, dict) or projected.get("schema") != 10:
        return None
    if not _SEPARATELY_REVALIDATED_FINGERPRINT_FIELDS <= set(projected):
        return None
    for field in _SEPARATELY_REVALIDATED_FINGERPRINT_FIELDS:
        projected.pop(field, None)
    return projected


def semantic_fingerprint_matches(stored: object, current: object) -> bool:
    """Compare all substantive non-Lean-container fingerprint coordinates."""

    stored_projection = semantic_fingerprint_projection(stored)
    current_projection = semantic_fingerprint_projection(current)
    return (
        stored_projection is not None
        and current_projection is not None
        and stored_projection == current_projection
    )


def _validated_raw_rows(
    raw_audit: Mapping[str, Any],
) -> tuple[dict[str, Mapping[str, Any]], str]:
    rows = raw_audit.get("configured_review_rows")
    if not isinstance(rows, list) or not rows:
        return {}, "canonical raw receipt has no configured review rows"
    indexed: dict[str, Mapping[str, Any]] = {}
    for row in rows:
        if not isinstance(row, Mapping):
            return {}, "canonical raw receipt has a malformed configured review row"
        qualified = str(row.get("qualified_declaration") or "").strip()
        signature = _sha256(row.get("elaborated_signature_sha256"))
        dependency = _sha256(row.get("semantic_dependency_sha256"))
        graph = configured_review_row_proposition_graph_sha256(row)
        if (
            not qualified
            or qualified in indexed
            or not signature
            or not dependency
            or not graph
        ):
            return {}, "canonical raw receipt has an ambiguous or unpinned review row"
        indexed[qualified] = row
    return indexed, ""


def manifest_matches_reviewed_semantic_payload(
    manifest: object,
    row: Mapping[str, Any],
) -> bool:
    """Match a current full manifest to a stored Lean semantic payload."""

    if not isinstance(manifest, Mapping):
        return False
    dependency = semantic_dependency_manifest(manifest)
    return (
        signature_manifest_digest(dict(manifest))
        == _sha256(row.get("elaborated_signature_sha256"))
        and _sha256(manifest.get("sha256"))
        == _sha256(row.get("elaborated_signature_sha256"))
        and isinstance(dependency, Mapping)
        and _sha256(dependency.get("semantic_dependency_sha256"))
        == _sha256(row.get("semantic_dependency_sha256"))
        and elaborated_proposition_graph_sha256(
            manifest.get("elaborated_proposition_graph")
        )
        == configured_review_row_proposition_graph_sha256(row)
    )


def manifest_root_matches_configured_row(
    manifest: object,
    row: Mapping[str, Any],
) -> bool:
    """Compare only the Lean-owned root meaning, excluding container hashes."""

    return bool(
        isinstance(manifest, Mapping)
        and signature_manifest_digest(dict(manifest))
        == _sha256(row.get("elaborated_signature_sha256"))
        and _sha256(manifest.get("sha256"))
        == _sha256(row.get("elaborated_signature_sha256"))
        and elaborated_proposition_graph_sha256(
            manifest.get("elaborated_proposition_graph")
        )
        == configured_review_row_proposition_graph_sha256(row)
    )


def configured_assumption_review_rows(
    raw_audit: Mapping[str, Any],
) -> Mapping[str, Mapping[str, Any]]:
    """Resolve the raw ledger's explicit assumption-role rows by declaration."""

    rows, row_error = _validated_raw_rows(raw_audit)
    if row_error:
        raise ValueError(row_error)
    raw_names = raw_audit.get("semantic_model_configured_assumption_rows")
    if raw_names is None:
        return {}
    if (
        not isinstance(raw_names, list)
        or any(not isinstance(name, str) or not name.strip() for name in raw_names)
        or len(set(raw_names)) != len(raw_names)
    ):
        raise ValueError("configured assumption-row inventory is malformed")
    by_row: dict[str, Mapping[str, Any]] = {}
    for row in rows.values():
        row_name = str(row.get("row") or "").strip()
        if row_name and row_name not in by_row:
            by_row[row_name] = row
        elif row_name:
            raise ValueError("configured review rows duplicate a row identifier")
    missing = sorted(set(raw_names) - set(by_row))
    if missing:
        raise ValueError(
            "configured assumption rows are absent from the raw review ledger: "
            + ", ".join(missing)
        )
    return {
        str(by_row[name]["qualified_declaration"]): by_row[name]
        for name in sorted(raw_names)
    }


def current_semantic_review_context_error(
    *,
    raw_audit: Mapping[str, Any],
    current_configured_review_declarations: set[str] | None,
    current_semantic_model_dimension_ids: set[str],
    current_source_proof_fidelity: Mapping[str, Any] | None,
    current_source_map_defect_ids: set[str],
) -> str:
    """Validate the non-Lean semantic-review controls shared by reuse lanes."""

    rows, row_error = _validated_raw_rows(raw_audit)
    if row_error:
        return row_error
    if (
        current_configured_review_declarations is not None
        and set(rows) != current_configured_review_declarations
    ):
        return "current configured review roots differ from the canonical receipt"

    raw_dimension_ids = {
        str(dimension.get("id") or "").strip()
        for item in raw_audit.get("semantic_model_items", [])
        if isinstance(item, Mapping)
        for dimension in item.get("dimensions", [])
        if isinstance(dimension, Mapping) and str(dimension.get("id") or "").strip()
    }
    if raw_dimension_ids != current_semantic_model_dimension_ids:
        return "current per-paper semantic-model dimensions differ from the canonical receipt"

    raw_fidelity = raw_audit.get("source_proof_fidelity")
    if raw_fidelity is not None and not isinstance(raw_fidelity, Mapping):
        return "canonical source-proof fidelity context is malformed"
    current_fidelity = (
        dict(current_source_proof_fidelity)
        if isinstance(current_source_proof_fidelity, Mapping)
        else None
    )
    for field in ("model_conventions", "checked_proof_steps"):
        prior = list(raw_fidelity.get(field) or []) if isinstance(raw_fidelity, Mapping) else []
        current = list(current_fidelity.get(field) or []) if current_fidelity else []
        if prior != current:
            return f"current source-proof fidelity {field} changed"
    current_defects = list(current_fidelity.get("defects") or []) if current_fidelity else []
    current_defect_ids = {
        str(defect.get("id") or "").strip()
        for defect in current_defects
        if isinstance(defect, Mapping) and str(defect.get("id") or "").strip()
    }
    if len(current_defect_ids) != len(current_defects):
        return "current source-proof fidelity defects are malformed or ambiguous"
    if not current_defect_ids <= current_source_map_defect_ids:
        return "current source-proof fidelity defect is not routed to the defect-review lane"
    return ""


def current_semantic_review_context_inputs(
    *,
    status: Mapping[str, Any],
    source_map: Mapping[str, Any],
    source_proof_fidelity: Mapping[str, Any] | None,
) -> tuple[set[str], set[str]]:
    """Normalize the live non-Lean context used by every semantic reuse lane."""

    review_surface = status.get("review_surface")
    semantic_config = (
        review_surface.get("semantic_model_review")
        if isinstance(review_surface, Mapping)
        else None
    )
    dimensions = (
        semantic_config.get("required_dimensions")
        if isinstance(semantic_config, Mapping)
        else None
    )
    if dimensions is None:
        dimension_ids: set[str] = set()
    elif not isinstance(dimensions, list) or not dimensions:
        raise ValueError("current semantic-model review configuration is malformed")
    else:
        normalized = [str(value).strip() for value in dimensions]
        if any(not value for value in normalized) or len(normalized) != len(
            set(normalized)
        ):
            raise ValueError(
                "current semantic-model dimensions are blank or duplicated"
            )
        dimension_ids = set(normalized)

    items = source_map.get("items")
    if not isinstance(items, Mapping):
        raise ValueError("current statement map has no item ledger")
    defect_ids = {
        defect.strip()
        for item in items.values()
        if isinstance(item, Mapping)
        for defect in item.get("source_defect_ids", [])
        if isinstance(defect, str) and defect.strip()
    }
    current_defects = (
        list(source_proof_fidelity.get("defects") or [])
        if isinstance(source_proof_fidelity, Mapping)
        else []
    )
    current_defect_ids = {
        str(defect.get("id") or "").strip()
        for defect in current_defects
        if isinstance(defect, Mapping) and str(defect.get("id") or "").strip()
    }
    if len(current_defect_ids) != len(current_defects):
        raise ValueError(
            "current source-proof fidelity defects are malformed or ambiguous"
        )
    return dimension_ids, defect_ids


def validate_current_semantic_reuse(
    *,
    root: Path,
    paper_dir: Path,
    raw_audit: Mapping[str, Any],
    current_import_module: str,
    current_semantic_dependency_modules: tuple[str, ...],
    current_configured_review_declarations: set[str],
    current_semantic_model_dimension_ids: set[str],
    current_source_proof_fidelity: Mapping[str, Any] | None,
    current_source_map_defect_ids: set[str],
    build_timeout_seconds: int = 600,
    build_input_provider: Any | None = None,
) -> tuple[dict[str, Any] | None, str]:
    """Validate one receipt against the current Lean semantic environment.

    Lean obtains fresh manifests for the canonical roots from the current
    import environment.  The authenticated carrier pins what those manifests
    must equal; it is not treated as a current cache merely because an engine
    or file coordinate happens to match.  This route writes no receipt and
    invents no human judgment.
    """

    rows, row_error = _validated_raw_rows(raw_audit)
    if row_error:
        return None, row_error
    context_error = current_semantic_review_context_error(
        raw_audit=raw_audit,
        current_configured_review_declarations=current_configured_review_declarations,
        current_semantic_model_dimension_ids=current_semantic_model_dimension_ids,
        current_source_proof_fidelity=current_source_proof_fidelity,
        current_source_map_defect_ids=current_source_map_defect_ids,
    )
    if context_error:
        return None, context_error
    raw_dimension_ids = {
        str(dimension.get("id") or "").strip()
        for item in raw_audit.get("semantic_model_items", [])
        if isinstance(item, Mapping)
        for dimension in item.get("dimensions", [])
        if isinstance(dimension, Mapping) and str(dimension.get("id") or "").strip()
    }
    current_defects = (
        list(current_source_proof_fidelity.get("defects") or [])
        if isinstance(current_source_proof_fidelity, Mapping)
        else []
    )
    current_defect_ids = {
        str(defect.get("id") or "").strip()
        for defect in current_defects
        if isinstance(defect, Mapping) and str(defect.get("id") or "").strip()
    }

    paper, contexts, stored_entries = validated_authenticated_manifest_store_entries(
        paper_dir
    )
    if paper != paper_dir.name:
        return None, "authenticated Lean manifest store is unavailable"

    for qualified, row in rows.items():
        pair = stored_entries.get(qualified)
        if pair is None:
            return None, f"authenticated Lean manifest is missing: {qualified}"
        entry, _manifest = pair
        if (
            _sha256(entry.get("elaborated_signature_sha256"))
            != _sha256(row.get("elaborated_signature_sha256"))
            or _sha256(entry.get("semantic_dependency_sha256"))
            != _sha256(row.get("semantic_dependency_sha256"))
            or _sha256(entry.get("elaborated_proposition_graph_sha256"))
            != configured_review_row_proposition_graph_sha256(row)
        ):
            return None, f"authenticated Lean manifest disagrees with receipt: {qualified}"
        context_id = str(entry.get("context_id") or "").strip()
        if context_id not in contexts:
            return None, f"authenticated Lean manifest context is missing: {qualified}"

    accepted: dict[str, dict[str, str]] = {}
    if not current_import_module or not current_semantic_dependency_modules:
        return None, "current Lean review environment is unavailable"
    # This function is entered only after the exact imported-source byte fast
    # path misses.  Building a context merely to ask whether an older context
    # can be reused duplicates work and makes comment/file-container changes
    # pay for historical cache machinery.  Ask Lean exactly once for the
    # current canonical roots instead.
    manifests = run_lean_signature_manifests(
        root,
        current_import_module,
        sorted(rows),
        timeout_seconds=120,
        build_timeout_seconds=build_timeout_seconds,
        semantic_dependency_modules=current_semantic_dependency_modules,
        build_input_provider=build_input_provider,
    )
    for qualified, row in rows.items():
        manifest = manifests.get(qualified) if isinstance(manifests, Mapping) else None
        if not manifest_matches_reviewed_semantic_payload(manifest, row):
            return None, f"current Lean semantic identity changed: {qualified}"
        accepted[qualified] = {
            "elaborated_signature_sha256": _sha256(
                row.get("elaborated_signature_sha256")
            ),
            "semantic_dependency_sha256": _sha256(
                row.get("semantic_dependency_sha256")
            ),
            "elaborated_proposition_graph_sha256": (
                configured_review_row_proposition_graph_sha256(row)
            ),
        }

    identity = {
        "reviewed_declarations": [
            {"qualified_declaration": qualified, **accepted[qualified]}
            for qualified in sorted(accepted)
        ],
    }
    return {
        "schema": SCHEMA,
        "policy": POLICY,
        "paper": paper_dir.name,
        "reviewed_declaration_count": len(accepted),
        "semantic_model_dimension_count": len(raw_dimension_ids),
        "separately_routed_proof_defect_count": len(current_defect_ids),
        "exact_context_count": 0,
        "fresh_context_count": 1,
        "semantic_identity_sha256": _canonical_sha256(identity),
        "current": True,
    }, ""
