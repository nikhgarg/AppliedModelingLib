#!/usr/bin/env python3
"""Persist Lean signature manifests behind a compact tracked authority.

The ignored carrier in ``.review_traces`` is never evidence by itself.  A row
is reusable only when its complete canonical JSON is pinned by the tracked
authority and the ordinary Lean manifest cache independently accepts the
current compiled context, signature, and semantic-dependency closure.
"""

from __future__ import annotations

import fcntl
import hashlib
import json
import os
import re
import tempfile
from contextlib import contextmanager
from pathlib import Path
from typing import Any, Callable, Iterable, Iterator, Mapping

try:
    from scripts.lean_signature_manifest import (
        reattach_semantic_dependency_module_identities,
        run_lean_signature_manifest_revalidations,
        seed_lean_signature_manifest_context_cache,
        semantic_dependency_manifest,
        signature_manifest_cache_context,
        signature_manifest_cache_context_sha256,
        signature_manifest_digest,
        signature_manifest_item_revalidation_matches,
    )
except ModuleNotFoundError:  # Direct ``python scripts/...`` execution.
    from lean_signature_manifest import (
        reattach_semantic_dependency_module_identities,
        run_lean_signature_manifest_revalidations,
        seed_lean_signature_manifest_context_cache,
        semantic_dependency_manifest,
        signature_manifest_cache_context,
        signature_manifest_cache_context_sha256,
        signature_manifest_digest,
        signature_manifest_item_revalidation_matches,
    )

try:
    from scripts.portable_evidence_identity import (
        portable_semantic_hash_tool_identity,
    )
except ModuleNotFoundError:  # Direct ``python scripts/...`` execution.
    from portable_evidence_identity import portable_semantic_hash_tool_identity


AUTHENTICATED_MANIFEST_AUTHORITY_SCHEMA = 1
AUTHENTICATED_MANIFEST_CARRIER_SCHEMA = 1
LEGACY_PAPER_INTERFACE_CACHE_SCHEMA = 20
AUTHORITY_FILENAME = "lean_signature_manifest_cache_authority.json"
CARRIER_FILENAME = "lean_signature_manifest_cache_carrier.json"
SHA256_RE = re.compile(r"[0-9a-f]{64}")


def authenticated_manifest_authority_path(paper_dir: Path) -> Path:
    """Return the compact, tracked authority path for one paper."""

    return paper_dir / "audit" / AUTHORITY_FILENAME


def authenticated_manifest_carrier_path(paper_dir: Path) -> Path:
    """Return the large, ignored manifest-carrier path for one paper."""

    return paper_dir / ".review_traces" / CARRIER_FILENAME


@contextmanager
def _authenticated_manifest_store_lock(paper_dir: Path) -> Iterator[None]:
    """Serialize one paper's two-file authenticated-store publication."""

    lock_path = authenticated_manifest_carrier_path(paper_dir).with_suffix(".lock")
    lock_path.parent.mkdir(parents=True, exist_ok=True)
    with lock_path.open("a+b") as handle:
        fcntl.flock(handle.fileno(), fcntl.LOCK_EX)
        try:
            yield
        finally:
            fcntl.flock(handle.fileno(), fcntl.LOCK_UN)


def canonical_json_sha256(value: object) -> str:
    """Hash one JSON value with a deterministic encoding."""

    try:
        encoded = json.dumps(
            value,
            sort_keys=True,
            separators=(",", ":"),
            ensure_ascii=True,
        ).encode("utf-8")
    except (TypeError, ValueError):
        return ""
    return hashlib.sha256(encoded).hexdigest()


def elaborated_proposition_graph_sha256(value: object) -> str:
    """Return the canonical digest of one complete graph-shaped payload."""

    return canonical_json_sha256(value) if isinstance(value, Mapping) else ""


def configured_review_row_proposition_graph_sha256(
    row: Mapping[str, Any],
) -> str:
    """Return one compact graph pin, accepting legacy embedded graph rows.

    Current raw audits retain only the canonical graph digest. Historical raw
    audits embedded the complete graph, so migration may derive the same pin
    from that body. If a transitional row contains both representations they
    must agree; neither field is allowed to override contradictory evidence.
    """

    explicit_key = "elaborated_proposition_graph_sha256"
    embedded_key = "elaborated_proposition_graph"
    explicit_present = explicit_key in row
    embedded_present = embedded_key in row
    explicit = _sha256(row.get(explicit_key))
    embedded = row.get(embedded_key)
    embedded_sha256 = elaborated_proposition_graph_sha256(embedded)
    if (explicit_present and not explicit) or (
        embedded_present and not embedded_sha256
    ):
        return ""
    if explicit and embedded_sha256 and explicit != embedded_sha256:
        return ""
    return explicit or embedded_sha256


def _sha256(value: object) -> str:
    text = str(value or "").strip().lower()
    return text if SHA256_RE.fullmatch(text) else ""


def declaration_authority_binding_sha256(
    *,
    qualified_declaration: str,
    authority_binding: Mapping[str, Any],
    elaborated_signature_sha256: str,
    semantic_dependency_sha256: str,
    elaborated_proposition_graph_sha256: str,
) -> str:
    """Bind one independently reconstructed declaration to its manifest.

    The compact store retains only the digest of the producer-specific
    ``authority_binding``.  That digest alone is not an authorization to seed:
    a forged authority could keep it while replacing the manifest identities.
    This projection couples that source-facing binding to every mathematical
    identity consumed by the manifest cache.  Prime callers must reconstruct
    this value from evidence outside the authority/carrier pair.
    """

    qualified = qualified_declaration.strip()
    binding_sha256 = canonical_json_sha256(authority_binding)
    signature = _sha256(elaborated_signature_sha256)
    dependency = _sha256(semantic_dependency_sha256)
    proposition_graph = _sha256(elaborated_proposition_graph_sha256)
    if (
        not qualified
        or not isinstance(authority_binding, Mapping)
        or not binding_sha256
        or not signature
        or not dependency
        or not proposition_graph
    ):
        return ""
    return canonical_json_sha256(
        {
            "qualified_declaration": qualified,
            "authority_binding_sha256": binding_sha256,
            "elaborated_signature_sha256": signature,
            "semantic_dependency_sha256": dependency,
            "elaborated_proposition_graph_sha256": proposition_graph,
        }
    )


def _stored_declaration_authority_binding_sha256(
    entry: Mapping[str, Any],
) -> str:
    """Return the full authority projection digest for one stored entry."""

    qualified = str(entry.get("qualified_declaration") or "").strip()
    binding = _sha256(entry.get("authority_binding_sha256"))
    signature = _sha256(entry.get("elaborated_signature_sha256"))
    dependency = _sha256(entry.get("semantic_dependency_sha256"))
    proposition_graph = _sha256(
        entry.get("elaborated_proposition_graph_sha256")
    )
    if not all((qualified, binding, signature, dependency, proposition_graph)):
        return ""
    return canonical_json_sha256(
        {
            "qualified_declaration": qualified,
            "authority_binding_sha256": binding,
            "elaborated_signature_sha256": signature,
            "semantic_dependency_sha256": dependency,
            "elaborated_proposition_graph_sha256": proposition_graph,
        }
    )


def _current_declaration_authority_binding_sha256(
    qualified_declaration: str,
    value: object,
) -> str:
    """Normalize one caller-owned binding envelope or exact projection pin."""

    if isinstance(value, str):
        return _sha256(value)
    if not isinstance(value, Mapping):
        return ""
    required = {
        "authority_binding",
        "elaborated_signature_sha256",
        "semantic_dependency_sha256",
        "elaborated_proposition_graph_sha256",
    }
    if set(value) != required or not isinstance(
        value.get("authority_binding"), Mapping
    ):
        return ""
    return declaration_authority_binding_sha256(
        qualified_declaration=qualified_declaration,
        authority_binding=value["authority_binding"],
        elaborated_signature_sha256=str(
            value.get("elaborated_signature_sha256") or ""
        ),
        semantic_dependency_sha256=str(
            value.get("semantic_dependency_sha256") or ""
        ),
        elaborated_proposition_graph_sha256=str(
            value.get("elaborated_proposition_graph_sha256") or ""
        ),
    )


_CURRENT_SOURCE_DECLARATION_FIELDS = {
    "source_file",
    "lean_source_declaration",
    "line_number",
    "declaration_kind",
}


def _current_source_declaration_coordinate(
    value: object,
) -> dict[str, object] | None:
    """Validate one current source coordinate used to bind a stored root.

    This is deliberately a source-coordinate check, not a declaration-name
    classifier.  The caller obtains the coordinate from its current review
    parser; this helper only accepts an exact file-relative declaration text,
    kind, and line.  A malformed coordinate is a cache miss before any
    carrier payload is considered.
    """

    if not isinstance(value, Mapping) or set(value) != _CURRENT_SOURCE_DECLARATION_FIELDS:
        return None
    source_file = str(value.get("source_file") or "").replace("\\", "/").strip()
    declaration = str(value.get("lean_source_declaration") or "").strip()
    kind = str(value.get("declaration_kind") or "").strip()
    line_number = value.get("line_number")
    path = Path(source_file)
    if (
        not source_file
        or path.is_absolute()
        or ".." in path.parts
        or source_file in {".", ".."}
        or not declaration
        or not kind
        or not isinstance(line_number, int)
        or line_number < 1
    ):
        return None
    return {
        "source_file": source_file,
        "lean_source_declaration": declaration,
        "line_number": line_number,
        "declaration_kind": kind,
    }


def current_source_bound_manifest_bindings(
    *,
    paper_dir: Path,
    current_declarations: Mapping[str, Mapping[str, object]],
) -> tuple[dict[str, dict[str, object]], dict[str, object]]:
    """Reconstruct exact current root bindings from tracked authority only.

    A compact tracked authority records the digest of the source coordinate
    used by its producer, while the ignored carrier holds the full Lean graph.
    For an unchanged compiled context, the current parser can independently
    rebuild that source coordinate without consulting a prior raw audit.  This
    function exposes only candidates whose rebuilt binding hash equals the
    tracked authority entry.  It never returns a manifest or reads the ignored
    carrier, so it cannot by itself establish semantic cache authority.

    The corresponding :func:`prime_authenticated_manifest_store` call still
    validates the carrier, exact current context, Lean-owned graph, and
    reattached module artifacts before it can seed an in-process cache.
    """

    authority = _load_json(authenticated_manifest_authority_path(paper_dir))
    entries = authority.get("entries")
    diagnostics: dict[str, object] = {
        "schema": 1,
        "paper": paper_dir.name,
        "requested_count": len(current_declarations),
        "candidate_count": 0,
        "accepted_binding_count": 0,
        "rejected_by_reason": {},
        "store_status": "unavailable_or_invalid_authority",
    }
    if (
        authority.get("schema") != AUTHENTICATED_MANIFEST_AUTHORITY_SCHEMA
        or authority.get("paper") != paper_dir.name
        or not isinstance(entries, list)
        or _sha256(authority.get("entries_sha256"))
        != canonical_json_sha256(entries)
    ):
        return {}, diagnostics

    indexed: dict[str, Mapping[str, object]] = {}
    duplicates: set[str] = set()
    for entry in entries:
        if not isinstance(entry, Mapping):
            diagnostics["store_status"] = "unavailable_or_invalid_authority"
            return {}, diagnostics
        qualified = str(entry.get("qualified_declaration") or "").strip()
        required = {
            "qualified_declaration",
            "context_id",
            "elaborated_signature_sha256",
            "semantic_dependency_sha256",
            "elaborated_proposition_graph_sha256",
            "manifest_payload_sha256",
            "authority_binding_sha256",
        }
        if (
            not qualified
            or set(entry) != required
            or not _sha256(entry.get("context_id"))
            or not all(
                _sha256(entry.get(field))
                for field in required
                - {"qualified_declaration", "context_id"}
            )
        ):
            diagnostics["store_status"] = "unavailable_or_invalid_authority"
            return {}, diagnostics
        if qualified in indexed:
            duplicates.add(qualified)
            indexed.pop(qualified, None)
        elif qualified not in duplicates:
            indexed[qualified] = entry

    rejected: dict[str, list[str]] = {}

    def reject(reason: str, qualified: str) -> None:
        rejected.setdefault(reason, []).append(qualified)

    bindings: dict[str, dict[str, object]] = {}
    for raw_qualified, raw_coordinate in current_declarations.items():
        qualified = str(raw_qualified).strip()
        if not qualified:
            continue
        if qualified in duplicates:
            reject("authority_declaration_ambiguous", qualified)
            continue
        entry = indexed.get(qualified)
        if entry is None:
            reject("authenticated_manifest_missing", qualified)
            continue
        coordinate = _current_source_declaration_coordinate(raw_coordinate)
        if coordinate is None:
            reject("current_source_coordinate_malformed", qualified)
            continue
        authority_binding = {
            "qualified_declaration": qualified,
            "source_file": coordinate["source_file"],
            "lean_source_declaration": coordinate["lean_source_declaration"],
            "line_number": coordinate["line_number"],
            "declaration_kind": coordinate["declaration_kind"],
            "elaborated_signature_sha256": entry[
                "elaborated_signature_sha256"
            ],
            "elaborated_proposition_graph_sha256": entry[
                "elaborated_proposition_graph_sha256"
            ],
        }
        binding = {
            "authority_binding": authority_binding,
            "elaborated_signature_sha256": entry[
                "elaborated_signature_sha256"
            ],
            "semantic_dependency_sha256": entry[
                "semantic_dependency_sha256"
            ],
            "elaborated_proposition_graph_sha256": entry[
                "elaborated_proposition_graph_sha256"
            ],
        }
        if (
            _current_declaration_authority_binding_sha256(qualified, binding)
            != _sha256(entry.get("authority_binding_sha256"))
        ):
            reject("current_source_binding_changed", qualified)
            continue
        bindings[qualified] = binding

    diagnostics["candidate_count"] = len(indexed)
    diagnostics["accepted_binding_count"] = len(bindings)
    diagnostics["rejected_by_reason"] = {
        reason: sorted(values)
        for reason, values in sorted(rejected.items())
        if values
    }
    diagnostics["store_status"] = "current_source_bindings_reconstructed"
    return bindings, diagnostics


def _context_authority(context: Mapping[str, Any]) -> dict[str, Any] | None:
    context_sha256 = signature_manifest_cache_context_sha256(context)
    import_module = str(context.get("import_module") or "").strip()
    raw_modules = context.get("audit_modules")
    if (
        not _sha256(context_sha256)
        or not import_module
        or not isinstance(raw_modules, list)
        or not raw_modules
        or any(not isinstance(module, str) or not module.strip() for module in raw_modules)
    ):
        return None
    modules = sorted(set(module.strip() for module in raw_modules))
    if modules != raw_modules or import_module not in modules:
        return None
    authority = {
        "import_module": import_module,
        "semantic_dependency_modules": modules,
        "manifest_cache_context_sha256": context_sha256,
    }
    authority["context_id"] = canonical_json_sha256(authority)
    return authority


def _manifest_entry(
    *,
    qualified_declaration: str,
    manifest: Mapping[str, Any],
    context: Mapping[str, Any],
    authority_binding: Mapping[str, Any],
) -> tuple[dict[str, Any], dict[str, Any], dict[str, Any]] | None:
    qualified = qualified_declaration.strip()
    context_authority = _context_authority(context)
    signature = signature_manifest_digest(manifest)
    dependency = semantic_dependency_manifest(manifest)
    dependency_sha256 = (
        _sha256(dependency.get("semantic_dependency_sha256"))
        if isinstance(dependency, Mapping)
        else ""
    )
    proposition_graph = manifest.get("elaborated_proposition_graph")
    proposition_graph_sha256 = elaborated_proposition_graph_sha256(
        proposition_graph
    )
    payload_sha256 = canonical_json_sha256(manifest)
    authority_binding_sha256 = canonical_json_sha256(authority_binding)
    if (
        not qualified
        or context_authority is None
        or not _sha256(signature)
        or _sha256(manifest.get("sha256")) != signature
        or not dependency_sha256
        or not isinstance(proposition_graph, Mapping)
        or not proposition_graph_sha256
        or not payload_sha256
        or not authority_binding_sha256
        or manifest.get("canonical_representation")
        != context.get("canonical_representation")
        or portable_semantic_hash_tool_identity(
            manifest.get("semantic_hash_tool_identity")
        )
        != portable_semantic_hash_tool_identity(
            context.get("semantic_hash_tool_identity")
        )
    ):
        return None
    authority_entry = {
        "qualified_declaration": qualified,
        "context_id": context_authority["context_id"],
        "elaborated_signature_sha256": signature,
        "semantic_dependency_sha256": dependency_sha256,
        "elaborated_proposition_graph_sha256": proposition_graph_sha256,
        "manifest_payload_sha256": payload_sha256,
        "authority_binding_sha256": authority_binding_sha256,
    }
    carrier_entry = {
        "qualified_declaration": qualified,
        "context_id": context_authority["context_id"],
        "manifest": dict(manifest),
    }
    return context_authority, authority_entry, carrier_entry


def build_authenticated_manifest_store_payloads(
    *,
    paper: str,
    candidates: Iterable[Mapping[str, Any]],
) -> tuple[dict[str, Any], dict[str, Any], set[str]]:
    """Build store payloads from independently successful exact candidates.

    Each candidate supplies ``qualified_declaration``, ``manifest``, ``context``,
    and an authority-specific ``authority_binding``.  Malformed or duplicate
    coordinates are omitted rather than receiving partial cache credit.
    """

    paper_id = paper.strip()
    prepared: dict[
        str, tuple[dict[str, Any], dict[str, Any], dict[str, Any]]
    ] = {}
    seen_names: set[str] = set()
    duplicate_names: set[str] = set()
    for candidate in candidates:
        if not isinstance(candidate, Mapping):
            continue
        qualified = str(candidate.get("qualified_declaration") or "").strip()
        manifest = candidate.get("manifest")
        context = candidate.get("context")
        binding = candidate.get("authority_binding")
        if not qualified:
            continue
        if qualified in seen_names:
            duplicate_names.add(qualified)
            prepared.pop(qualified, None)
            continue
        seen_names.add(qualified)
        if (
            not isinstance(manifest, Mapping)
            or not isinstance(context, Mapping)
            or not isinstance(binding, Mapping)
        ):
            continue
        entry = _manifest_entry(
            qualified_declaration=qualified,
            manifest=manifest,
            context=context,
            authority_binding=binding,
        )
        if entry is not None:
            prepared[qualified] = entry
    for qualified in duplicate_names:
        prepared.pop(qualified, None)

    contexts_by_id = {
        entry[0]["context_id"]: entry[0]
        for entry in prepared.values()
    }
    contexts = [contexts_by_id[key] for key in sorted(contexts_by_id)]
    authority_entries = [prepared[key][1] for key in sorted(prepared)]
    carrier_entries = [prepared[key][2] for key in sorted(prepared)]
    authority = {
        "schema": AUTHENTICATED_MANIFEST_AUTHORITY_SCHEMA,
        "paper": paper_id,
        "contexts": contexts,
        "contexts_sha256": canonical_json_sha256(contexts),
        "entries": authority_entries,
        "entries_sha256": canonical_json_sha256(authority_entries),
    }
    carrier = {
        "schema": AUTHENTICATED_MANIFEST_CARRIER_SCHEMA,
        "paper": paper_id,
        "entries": carrier_entries,
    }
    return authority, carrier, set(prepared)


def _atomic_write_json(path: Path, payload: Mapping[str, Any]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    encoded = json.dumps(payload, indent=2, sort_keys=True) + "\n"
    descriptor, temporary_name = tempfile.mkstemp(
        prefix=f".{path.name}.", suffix=".tmp", dir=path.parent
    )
    temporary = Path(temporary_name)
    try:
        with os.fdopen(descriptor, "w", encoding="utf-8") as handle:
            handle.write(encoded)
            handle.flush()
            os.fsync(handle.fileno())
        os.replace(temporary, path)
    finally:
        try:
            temporary.unlink()
        except FileNotFoundError:
            pass


def publish_authenticated_manifest_store(
    *,
    paper_dir: Path,
    paper: str,
    candidates: Iterable[Mapping[str, Any]],
) -> set[str]:
    """Atomically publish exact entries, writing the carrier before authority."""

    authority, carrier, accepted = build_authenticated_manifest_store_payloads(
        paper=paper,
        candidates=candidates,
    )
    with _authenticated_manifest_store_lock(paper_dir):
        _atomic_write_json(authenticated_manifest_carrier_path(paper_dir), carrier)
        _atomic_write_json(authenticated_manifest_authority_path(paper_dir), authority)
    return accepted


def _load_json(path: Path) -> dict[str, Any]:
    try:
        value = json.loads(path.read_text(encoding="utf-8"))
    except (OSError, UnicodeDecodeError, json.JSONDecodeError):
        return {}
    return value if isinstance(value, dict) else {}


def validated_manifest_store_payloads(
    *,
    paper: str,
    authority: Mapping[str, Any],
    carrier: Mapping[str, Any],
) -> tuple[
    dict[str, dict[str, Any]],
    dict[str, tuple[dict[str, Any], dict[str, Any]]],
] | None:
    """Validate an authority/carrier pair supplied as exact in-memory payloads.

    The ordinary on-disk store and an immutable historical-recovery receipt use
    the same structural contract.  Keeping this validation independent of a
    filesystem path lets a recovery consumer verify decompressed, receipt-pinned
    bytes before it considers any declaration coordinate.  It deliberately
    returns ``None`` for a malformed pair; an empty but valid store remains a
    valid empty result.
    """

    expected_paper = str(paper or "").strip()
    if not expected_paper:
        return None
    contexts = authority.get("contexts")
    entries = authority.get("entries")
    carrier_entries = carrier.get("entries")
    if (
        authority.get("schema") != AUTHENTICATED_MANIFEST_AUTHORITY_SCHEMA
        or carrier.get("schema") != AUTHENTICATED_MANIFEST_CARRIER_SCHEMA
        or authority.get("paper") != expected_paper
        or carrier.get("paper") != expected_paper
        or not isinstance(contexts, list)
        or not isinstance(entries, list)
        or not isinstance(carrier_entries, list)
        or _sha256(authority.get("contexts_sha256"))
        != canonical_json_sha256(contexts)
        or _sha256(authority.get("entries_sha256"))
        != canonical_json_sha256(entries)
    ):
        return None

    contexts_by_id: dict[str, dict[str, Any]] = {}
    for raw_context in contexts:
        if not isinstance(raw_context, dict):
            return None
        context_id = _sha256(raw_context.get("context_id"))
        projection = {
            key: raw_context.get(key)
            for key in (
                "import_module",
                "semantic_dependency_modules",
                "manifest_cache_context_sha256",
            )
        }
        if (
            set(raw_context) != {*projection, "context_id"}
            or not context_id
            or canonical_json_sha256(projection) != context_id
            or context_id in contexts_by_id
            or not isinstance(projection["import_module"], str)
            or not str(projection["import_module"]).strip()
            or not isinstance(projection["semantic_dependency_modules"], list)
            or projection["semantic_dependency_modules"]
            != sorted(set(projection["semantic_dependency_modules"]))
            or projection["import_module"]
            not in projection["semantic_dependency_modules"]
            or not _sha256(projection["manifest_cache_context_sha256"])
        ):
            return None
        contexts_by_id[context_id] = raw_context

    carrier_by_coordinate: dict[tuple[str, str], Mapping[str, Any]] = {}
    for raw_carrier in carrier_entries:
        if not isinstance(raw_carrier, Mapping):
            return None
        coordinate = (
            str(raw_carrier.get("qualified_declaration") or "").strip(),
            _sha256(raw_carrier.get("context_id")),
        )
        if (
            set(raw_carrier) != {"qualified_declaration", "context_id", "manifest"}
            or not all(coordinate)
            or coordinate in carrier_by_coordinate
            or not isinstance(raw_carrier.get("manifest"), Mapping)
        ):
            return None
        carrier_by_coordinate[coordinate] = raw_carrier

    authority_name_counts: dict[str, int] = {}
    for raw_entry in entries:
        if not isinstance(raw_entry, dict):
            return None
        qualified = str(raw_entry.get("qualified_declaration") or "").strip()
        if qualified:
            authority_name_counts[qualified] = (
                authority_name_counts.get(qualified, 0) + 1
            )
    duplicate_authority_names = {
        qualified
        for qualified, count in authority_name_counts.items()
        if count > 1
    }

    validated: dict[str, tuple[dict[str, Any], dict[str, Any]]] = {}
    for raw_entry in entries:
        required = {
            "qualified_declaration",
            "context_id",
            "elaborated_signature_sha256",
            "semantic_dependency_sha256",
            "elaborated_proposition_graph_sha256",
            "manifest_payload_sha256",
            "authority_binding_sha256",
        }
        qualified = str(raw_entry.get("qualified_declaration") or "").strip()
        context_id = _sha256(raw_entry.get("context_id"))
        carrier_entry = carrier_by_coordinate.get((qualified, context_id))
        manifest = carrier_entry.get("manifest") if carrier_entry else None
        if (
            set(raw_entry) != required
            or not qualified
            or qualified in duplicate_authority_names
            or qualified in validated
            or context_id not in contexts_by_id
            or not all(_sha256(raw_entry.get(field)) for field in required - {"qualified_declaration", "context_id"})
            or not isinstance(manifest, Mapping)
            or canonical_json_sha256(manifest)
            != _sha256(raw_entry.get("manifest_payload_sha256"))
            or signature_manifest_digest(manifest)
            != _sha256(raw_entry.get("elaborated_signature_sha256"))
            or _sha256(manifest.get("sha256"))
            != _sha256(raw_entry.get("elaborated_signature_sha256"))
            or elaborated_proposition_graph_sha256(
                manifest.get("elaborated_proposition_graph")
            )
            != _sha256(raw_entry.get("elaborated_proposition_graph_sha256"))
        ):
            continue
        dependency = semantic_dependency_manifest(manifest)
        if (
            not isinstance(dependency, Mapping)
            or _sha256(dependency.get("semantic_dependency_sha256"))
            != _sha256(raw_entry.get("semantic_dependency_sha256"))
        ):
            continue
        validated[qualified] = (raw_entry, dict(manifest))
    return contexts_by_id, validated


def _validated_store_entries(
    paper_dir: Path,
) -> tuple[
    str,
    dict[str, dict[str, Any]],
    dict[str, tuple[dict[str, Any], dict[str, Any]]],
]:
    authority = _load_json(authenticated_manifest_authority_path(paper_dir))
    carrier = _load_json(authenticated_manifest_carrier_path(paper_dir))
    paper = str(authority.get("paper") or "").strip()
    validated = validated_manifest_store_payloads(
        paper=paper,
        authority=authority,
        carrier=carrier,
    )
    if validated is None or paper != paper_dir.name:
        return "", {}, {}
    contexts_by_id, entries = validated
    return paper, contexts_by_id, entries


def validated_authenticated_manifest_store_entries(
    paper_dir: Path,
) -> tuple[
    str,
    dict[str, dict[str, Any]],
    dict[str, tuple[dict[str, Any], dict[str, Any]]],
]:
    """Return the structurally validated tracked-authority/carrier store.

    This public read-only projection is for current semantic verifiers.  It
    grants no cache credit by itself: callers must independently bind every
    requested declaration to current Lean output and compare the stored
    signature, proposition graph, and semantic dependency identities.
    """

    return _validated_store_entries(paper_dir)


def merge_authenticated_manifest_store(
    *,
    paper_dir: Path,
    paper: str,
    candidates: Iterable[Mapping[str, Any]],
) -> set[str]:
    """Upsert exact candidates without shrinking another producer's subset.

    Every supplied qualified name replaces its prior coordinate, including
    when the supplied candidate is malformed and therefore cannot be written.
    Unmentioned entries survive only when the existing authority/carrier pair
    validates structurally. Current-context validation and requested-root
    projection remain the responsibility of the ordinary prime consumer.
    """

    candidate_list = list(candidates)
    attempted_names = {
        str(candidate.get("qualified_declaration") or "").strip()
        for candidate in candidate_list
        if isinstance(candidate, Mapping)
        and str(candidate.get("qualified_declaration") or "").strip()
    }
    new_authority, new_carrier, _new_accepted = (
        build_authenticated_manifest_store_payloads(
            paper=paper,
            candidates=candidate_list,
        )
    )
    paper_id = paper.strip()

    with _authenticated_manifest_store_lock(paper_dir):
        stored_paper, stored_contexts, stored_entries = _validated_store_entries(
            paper_dir
        )
        if stored_paper != paper_id:
            stored_contexts = {}
            stored_entries = {}

        contexts_by_id: dict[str, dict[str, Any]] = {}
        authority_entries_by_name: dict[str, dict[str, Any]] = {}
        carrier_entries_by_name: dict[str, dict[str, Any]] = {}
        for qualified, (authority_entry, manifest) in stored_entries.items():
            if qualified in attempted_names:
                continue
            context_id = str(authority_entry.get("context_id") or "").strip()
            context = stored_contexts.get(context_id)
            if not isinstance(context, Mapping):
                continue
            contexts_by_id[context_id] = dict(context)
            authority_entries_by_name[qualified] = dict(authority_entry)
            carrier_entries_by_name[qualified] = {
                "qualified_declaration": qualified,
                "context_id": context_id,
                "manifest": dict(manifest),
            }

        new_contexts_by_id = {
            str(context.get("context_id") or "").strip(): dict(context)
            for context in new_authority.get("contexts", [])
            if isinstance(context, Mapping)
            and str(context.get("context_id") or "").strip()
        }
        new_carriers_by_coordinate = {
            (
                str(entry.get("qualified_declaration") or "").strip(),
                str(entry.get("context_id") or "").strip(),
            ): dict(entry)
            for entry in new_carrier.get("entries", [])
            if isinstance(entry, Mapping)
        }
        for raw_entry in new_authority.get("entries", []):
            if not isinstance(raw_entry, Mapping):
                continue
            qualified = str(raw_entry.get("qualified_declaration") or "").strip()
            context_id = str(raw_entry.get("context_id") or "").strip()
            context = new_contexts_by_id.get(context_id)
            carrier_entry = new_carriers_by_coordinate.get((qualified, context_id))
            if (
                not qualified
                or not isinstance(context, Mapping)
                or not isinstance(carrier_entry, Mapping)
            ):
                continue
            prior_context = contexts_by_id.get(context_id)
            if prior_context is not None and prior_context != context:
                # A context id is a digest of the complete compact context.
                # Conflicting bodies therefore invalidate preserved users of
                # that coordinate rather than relying on either body.
                for prior_name, prior_entry in list(
                    authority_entries_by_name.items()
                ):
                    if prior_entry.get("context_id") == context_id:
                        authority_entries_by_name.pop(prior_name, None)
                        carrier_entries_by_name.pop(prior_name, None)
            contexts_by_id[context_id] = dict(context)
            authority_entries_by_name[qualified] = dict(raw_entry)
            carrier_entries_by_name[qualified] = dict(carrier_entry)

        used_context_ids = {
            str(entry.get("context_id") or "").strip()
            for entry in authority_entries_by_name.values()
        }
        contexts = [
            contexts_by_id[context_id]
            for context_id in sorted(used_context_ids)
            if context_id in contexts_by_id
        ]
        authority_entries = [
            authority_entries_by_name[name]
            for name in sorted(authority_entries_by_name)
        ]
        carrier_entries = [
            carrier_entries_by_name[name]
            for name in sorted(carrier_entries_by_name)
        ]
        authority = {
            "schema": AUTHENTICATED_MANIFEST_AUTHORITY_SCHEMA,
            "paper": paper_id,
            "contexts": contexts,
            "contexts_sha256": canonical_json_sha256(contexts),
            "entries": authority_entries,
            "entries_sha256": canonical_json_sha256(authority_entries),
        }
        carrier = {
            "schema": AUTHENTICATED_MANIFEST_CARRIER_SCHEMA,
            "paper": paper_id,
            "entries": carrier_entries,
        }
        _atomic_write_json(authenticated_manifest_carrier_path(paper_dir), carrier)
        _atomic_write_json(authenticated_manifest_authority_path(paper_dir), authority)
    return set(authority_entries_by_name)


def prime_authenticated_manifest_store(
    *,
    root: Path,
    paper_dir: Path,
    current_declaration_bindings: Mapping[str, Mapping[str, Any] | str],
    current_contexts: Iterable[Mapping[str, Any]] = (),
    requested_declarations: Iterable[str] | None = None,
    semantic_revalidated_bindings: Mapping[str, Mapping[str, str]] | None = None,
    build_timeout_seconds: int = 600,
    context_provider: Callable[..., Mapping[str, Any] | None] = signature_manifest_cache_context,
    reattach: Callable[..., dict[str, dict[str, Any]]] = reattach_semantic_dependency_module_identities,
    seed: Callable[..., set[str]] = seed_lean_signature_manifest_context_cache,
) -> tuple[dict[str, dict[str, Any]], dict[str, Any]]:
    """Revalidate and seed entries bound to independent current authority.

    ``current_declaration_bindings`` must not be reconstructed from the
    authority/carrier pair being primed.  Each value is either an exact digest
    returned by :func:`declaration_authority_binding_sha256` or a strict
    envelope containing ``authority_binding`` and the three manifest identity
    fields accepted by that helper.  Missing, malformed, and changed bindings
    are cache misses before any reattachment or seed operation.

    ``semantic_revalidated_bindings`` is a declaration-local handoff from one
    completed current Lean pass. It may rebind a stored full manifest to a new
    compiled cache context only when the signature, dependency, and
    proposition-graph identities all match independently supplied current
    bindings. It never accepts a declaration by name alone.
    """

    paper, contexts_by_id, entries = _validated_store_entries(paper_dir)
    requested = (
        {
            str(qualified).strip()
            for qualified in requested_declarations
            if str(qualified).strip()
        }
        if requested_declarations is not None
        else None
    )
    if requested is not None:
        entries = {
            qualified: pair
            for qualified, pair in entries.items()
            if qualified in requested
        }
    diagnostics: dict[str, Any] = {
        "schema": 1,
        "paper": paper_dir.name,
        "candidate_count": len(entries),
        "requested_count": len(requested) if requested is not None else len(entries),
        "context_count": len(contexts_by_id),
        "accepted_context_count": 0,
        "context_provider_call_count": 0,
        "seeded_count": 0,
        "seeded_declarations": [],
        "fresh_required_count": len(entries),
        "rejected_by_reason": {},
    }
    if not paper or not entries:
        diagnostics["store_status"] = "unavailable_empty_or_invalid"
        return {}, diagnostics
    supplied_contexts: dict[str, Mapping[str, Any]] = {}
    ambiguous_supplied_contexts: set[str] = set()
    for context in current_contexts:
        if not isinstance(context, Mapping):
            continue
        import_module = str(context.get("import_module") or "").strip()
        if not import_module:
            continue
        prior = supplied_contexts.get(import_module)
        if prior is not None and dict(prior) != dict(context):
            ambiguous_supplied_contexts.add(import_module)
            supplied_contexts.pop(import_module, None)
        elif import_module not in ambiguous_supplied_contexts:
            supplied_contexts[import_module] = context

    rejected: dict[str, set[str]] = {}
    semantic_revalidated = {
        str(qualified).strip(): dict(raw)
        for qualified, raw in (semantic_revalidated_bindings or {}).items()
        if str(qualified).strip() and isinstance(raw, Mapping)
    }

    def reject(reason: str, declarations: Iterable[str]) -> None:
        rejected.setdefault(reason, set()).update(
            declaration for declaration in declarations if declaration
        )

    accepted: dict[str, dict[str, Any]] = {}
    accepted_context_count = 0
    context_provider_call_count = 0
    for context_id, authority_context in sorted(contexts_by_id.items()):
        import_module = str(authority_context["import_module"])
        modules = tuple(authority_context["semantic_dependency_modules"])
        group = {
            qualified: manifest
            for qualified, (entry, manifest) in entries.items()
            if entry["context_id"] == context_id
        }
        binding_accepted: dict[str, dict[str, Any]] = {}
        for qualified, manifest in group.items():
            if qualified not in current_declaration_bindings:
                reject("current_declaration_binding_missing", [qualified])
                continue
            current_binding_sha256 = (
                _current_declaration_authority_binding_sha256(
                    qualified,
                    current_declaration_bindings[qualified],
                )
            )
            if not current_binding_sha256:
                reject("current_declaration_binding_malformed", [qualified])
                continue
            entry = entries[qualified][0]
            if (
                current_binding_sha256
                != _stored_declaration_authority_binding_sha256(entry)
            ):
                semantic_binding = semantic_revalidated.get(qualified)
                current_binding = current_declaration_bindings.get(qualified)
                if not isinstance(semantic_binding, Mapping) or not isinstance(
                    current_binding, Mapping
                ) or any(
                    _sha256(semantic_binding.get(field))
                    != _sha256(current_binding.get(field))
                    or _sha256(semantic_binding.get(field))
                    != _sha256(entry.get(field))
                    for field in (
                        "elaborated_signature_sha256",
                        "semantic_dependency_sha256",
                        "elaborated_proposition_graph_sha256",
                    )
                ):
                    reject("current_declaration_binding_changed", [qualified])
                    continue
            binding_accepted[qualified] = manifest
        group = binding_accepted
        if not group:
            continue
        if import_module in ambiguous_supplied_contexts:
            reject("ambiguous_supplied_current_context", group)
            continue
        current_context = supplied_contexts.get(import_module)
        if current_context is None:
            context_provider_call_count += 1
            try:
                current_context = context_provider(
                    root,
                    import_module,
                    build_timeout_seconds=build_timeout_seconds,
                    semantic_dependency_modules=modules,
                )
            except Exception:  # noqa: BLE001 - a cache probe must fail closed.
                current_context = None
        if not isinstance(current_context, Mapping):
            reject("current_context_unavailable", group)
            continue
        current_context_sha256 = signature_manifest_cache_context_sha256(
            current_context
        )
        if current_context_sha256 != authority_context["manifest_cache_context_sha256"]:
            rebound_group: dict[str, dict[str, Any]] = {}
            for qualified, manifest in group.items():
                expected = semantic_revalidated.get(qualified)
                binding = current_declaration_bindings.get(qualified)
                if not isinstance(expected, Mapping) or not isinstance(
                    binding, Mapping
                ):
                    reject("current_context_identity_changed", [qualified])
                    continue
                if any(
                    _sha256(expected.get(field)) != _sha256(binding.get(field))
                    for field in (
                        "elaborated_signature_sha256",
                        "semantic_dependency_sha256",
                        "elaborated_proposition_graph_sha256",
                    )
                ):
                    reject("semantic_revalidation_binding_changed", [qualified])
                    continue
                rebound_group[qualified] = manifest
            group = rebound_group
            if not group:
                continue
        accepted_context_count += 1
        try:
            rebound = reattach(
                root,
                group,
                timeout_seconds=build_timeout_seconds,
            )
        except Exception:  # noqa: BLE001 - missing current artifacts are misses.
            rebound = {}
        if not isinstance(rebound, Mapping):
            rebound = {}
        candidates: dict[str, dict[str, Any]] = {}
        pins: dict[str, dict[str, str]] = {}
        for qualified in group:
            manifest = rebound.get(qualified)
            if not isinstance(manifest, Mapping):
                reject("module_identity_reattachment_failed", [qualified])
                continue
            pair = entries.get(qualified)
            if pair is None or pair[0]["context_id"] != context_id:
                reject("stored_context_coordinate_changed", [qualified])
                continue
            authority_entry = pair[0]
            dependency = semantic_dependency_manifest(manifest)
            if signature_manifest_digest(manifest) != authority_entry[
                "elaborated_signature_sha256"
            ]:
                reject("elaborated_signature_identity_changed", [qualified])
                continue
            if not isinstance(dependency, Mapping):
                reject("semantic_dependency_identity_unavailable", [qualified])
                continue
            if (
                _sha256(dependency.get("semantic_dependency_sha256"))
                != authority_entry["semantic_dependency_sha256"]
            ):
                reject("semantic_dependency_identity_changed", [qualified])
                continue
            if (
                elaborated_proposition_graph_sha256(
                    manifest.get("elaborated_proposition_graph")
                )
                != authority_entry["elaborated_proposition_graph_sha256"]
            ):
                reject("elaborated_proposition_graph_identity_changed", [qualified])
                continue
            current_manifest = dict(manifest)
            current_manifest["semantic_dependency_manifest"] = dict(dependency)
            candidates[qualified] = current_manifest
            pins[qualified] = {
                "manifest_cache_context_sha256": current_context_sha256,
                "elaborated_signature_sha256": authority_entry[
                    "elaborated_signature_sha256"
                ],
                "semantic_dependency_sha256": authority_entry[
                    "semantic_dependency_sha256"
                ],
            }
        if not candidates:
            continue
        try:
            seeded = seed(
                root,
                import_module,
                candidates,
                pins,
                build_timeout_seconds=build_timeout_seconds,
                semantic_dependency_modules=modules,
                current_context=current_context,
            )
        except Exception:  # noqa: BLE001 - seed rejection must stay a miss.
            seeded = set()
        reject("context_cache_seed_rejected", set(candidates) - set(seeded))
        for qualified in seeded:
            if qualified in candidates:
                accepted[qualified] = candidates[qualified]
    diagnostics["store_status"] = "validated"
    diagnostics["accepted_context_count"] = accepted_context_count
    diagnostics["context_provider_call_count"] = context_provider_call_count
    diagnostics["seeded_count"] = len(accepted)
    diagnostics["seeded_declarations"] = sorted(accepted)
    diagnostics["fresh_required_count"] = len(entries) - len(accepted)
    diagnostics["rejected_by_reason"] = {
        reason: sorted(declarations)
        for reason, declarations in sorted(rejected.items())
        if declarations
    }
    return accepted, diagnostics


_RESUME_LEAN_PAYLOAD_FIELDS = (
    "schema",
    "declaration_kind",
    "conclusion_mode",
    "atoms",
    "elaborated_execution_state_refinement_shape",
    "elaborated_proposition_graph",
    "elaborated_transparent_result_value_graph",
    "semantic_dependency_graph",
    "sha256",
)


def _resume_lean_payload_matches_carrier(
    resume_manifest: object,
    carrier_manifest: Mapping[str, Any],
    authority_entry: Mapping[str, Any],
) -> bool:
    """Require an ignored resume payload to be byte-for-byte carrier-equivalent.

    A resume record may prove only that the current source parser still sees
    the same declaration coordinate.  Its Lean payload is never accepted on
    its own: all Lean-emitted fields must exactly match the authenticated
    carrier whose signature and proposition-graph pins were already checked
    against tracked authority.
    """

    if not isinstance(resume_manifest, Mapping):
        return False
    if any(field not in resume_manifest for field in _RESUME_LEAN_PAYLOAD_FIELDS):
        return False
    if any(
        resume_manifest.get(field) != carrier_manifest.get(field)
        for field in _RESUME_LEAN_PAYLOAD_FIELDS
    ):
        return False
    return (
        signature_manifest_digest(dict(resume_manifest))
        == _sha256(authority_entry.get("elaborated_signature_sha256"))
        and elaborated_proposition_graph_sha256(
            resume_manifest.get("elaborated_proposition_graph")
        )
        == _sha256(authority_entry.get("elaborated_proposition_graph_sha256"))
    )


def prime_exact_context_attested_resume_manifests(
    *,
    root: Path,
    paper_dir: Path,
    import_module: str,
    semantic_dependency_modules: tuple[str, ...],
    current_context: Mapping[str, Any],
    current_bindings: Mapping[str, Mapping[str, Any]],
    resume_records: Mapping[str, Mapping[str, Any]],
    reattach: Callable[..., dict[str, dict[str, Any]]] = (
        reattach_semantic_dependency_module_identities
    ),
    seed: Callable[..., set[str]] = seed_lean_signature_manifest_context_cache,
) -> tuple[dict[str, dict[str, Any]], dict[str, Any]]:
    """Seed exact-context rows only when journal, authority, and carrier agree.

    This is a resource-bounded compatibility path for journal records written
    before a producer retained a reconstructable authority-binding body.  The
    journal is explicitly non-authoritative: a record can only provide a
    current-source coordinate after its binding equals the caller's current
    parser binding.  The Lean payload used for seeding always comes from the
    authenticated carrier, and the journal copy must exactly equal that carrier
    on every Lean-emitted payload field.  Exact current context and reattached
    Lean-owned dependency artifacts remain mandatory.

    A context change, missing carrier, malformed row, or any disagreement is a
    cache miss.  In particular this function never invokes item revalidation;
    callers must obtain fresh full manifests for misses.
    """

    paper, contexts_by_id, entries = _validated_store_entries(paper_dir)
    requested = {
        str(qualified).strip()
        for qualified in current_bindings
        if str(qualified).strip()
    }
    diagnostics: dict[str, Any] = {
        "schema": 1,
        "paper": paper_dir.name,
        "requested_count": len(requested),
        "candidate_count": 0,
        "seeded_count": 0,
        "seeded_declarations": [],
        "fresh_required_count": len(requested),
        "rejected_by_reason": {},
        "store_status": "unavailable_empty_or_invalid",
    }
    if paper != paper_dir.name or not requested or not entries:
        return {}, diagnostics

    current_authority = _context_authority(current_context)
    if current_authority is None:
        diagnostics["store_status"] = "current_context_malformed"
        return {}, diagnostics
    context_id = str(current_authority.get("context_id") or "").strip()
    stored_context = contexts_by_id.get(context_id)
    if (
        not isinstance(stored_context, Mapping)
        or str(stored_context.get("import_module") or "").strip()
        != import_module
        or tuple(stored_context.get("semantic_dependency_modules") or ())
        != tuple(semantic_dependency_modules)
    ):
        diagnostics["store_status"] = "exact_context_unavailable"
        return {}, diagnostics

    rejected: dict[str, set[str]] = {}

    def reject(reason: str, qualified: str) -> None:
        rejected.setdefault(reason, set()).add(qualified)

    candidates: dict[str, dict[str, Any]] = {}
    for qualified in sorted(requested):
        current_binding = current_bindings.get(qualified)
        resume = resume_records.get(qualified)
        pair = entries.get(qualified)
        if not isinstance(current_binding, Mapping):
            reject("current_source_binding_malformed", qualified)
            continue
        if not isinstance(resume, Mapping):
            reject("resume_record_missing", qualified)
            continue
        resume_binding = resume.get("binding")
        resume_manifest = resume.get("manifest")
        if not isinstance(resume_binding, Mapping) or dict(resume_binding) != dict(
            current_binding
        ):
            reject("resume_binding_changed", qualified)
            continue
        if pair is None:
            reject("authenticated_manifest_missing", qualified)
            continue
        authority_entry, carrier_manifest = pair
        if str(authority_entry.get("context_id") or "").strip() != context_id:
            reject("authenticated_context_changed", qualified)
            continue
        if not _resume_lean_payload_matches_carrier(
            resume_manifest, carrier_manifest, authority_entry
        ):
            reject("resume_payload_not_attested", qualified)
            continue
        candidates[qualified] = dict(carrier_manifest)

    diagnostics["candidate_count"] = len(candidates)
    if not candidates:
        diagnostics["store_status"] = "validated_exact_context_no_candidates"
        diagnostics["rejected_by_reason"] = {
            reason: sorted(values)
            for reason, values in sorted(rejected.items())
            if values
        }
        return {}, diagnostics

    try:
        rebound = reattach(root, candidates, timeout_seconds=600)
    except Exception:  # noqa: BLE001 - resume optimization must fail closed.
        rebound = {}
    if not isinstance(rebound, Mapping):
        rebound = {}

    accepted_candidates: dict[str, dict[str, Any]] = {}
    pins: dict[str, dict[str, str]] = {}
    current_context_sha = signature_manifest_cache_context_sha256(current_context)
    for qualified in sorted(candidates):
        current_manifest = rebound.get(qualified)
        pair = entries.get(qualified)
        if not isinstance(current_manifest, Mapping) or pair is None:
            reject("current_dependency_artifacts_unavailable", qualified)
            continue
        authority_entry, _carrier = pair
        dependency = semantic_dependency_manifest(current_manifest)
        if (
            signature_manifest_digest(dict(current_manifest))
            != _sha256(authority_entry.get("elaborated_signature_sha256"))
            or elaborated_proposition_graph_sha256(
                current_manifest.get("elaborated_proposition_graph")
            )
            != _sha256(authority_entry.get("elaborated_proposition_graph_sha256"))
            or not isinstance(dependency, Mapping)
            or _sha256(dependency.get("semantic_dependency_sha256"))
            != _sha256(authority_entry.get("semantic_dependency_sha256"))
        ):
            reject("current_manifest_identity_changed", qualified)
            continue
        manifest = dict(current_manifest)
        manifest["semantic_dependency_manifest"] = dict(dependency)
        accepted_candidates[qualified] = manifest
        pins[qualified] = {
            "manifest_cache_context_sha256": current_context_sha,
            "elaborated_signature_sha256": _sha256(
                authority_entry.get("elaborated_signature_sha256")
            ),
            "semantic_dependency_sha256": _sha256(
                authority_entry.get("semantic_dependency_sha256")
            ),
        }

    accepted: dict[str, dict[str, Any]] = {}
    if accepted_candidates:
        try:
            seeded = seed(
                root,
                import_module,
                accepted_candidates,
                pins,
                semantic_dependency_modules=semantic_dependency_modules,
                current_context=current_context,
            )
        except Exception:  # noqa: BLE001 - resume optimization must fail closed.
            seeded = set()
        for qualified in seeded:
            manifest = accepted_candidates.get(qualified)
            if manifest is not None:
                accepted[qualified] = manifest
        for qualified in set(accepted_candidates) - set(seeded):
            reject("context_cache_seed_rejected", qualified)

    diagnostics["store_status"] = "validated_exact_context_resume_attestation"
    diagnostics["seeded_count"] = len(accepted)
    diagnostics["seeded_declarations"] = sorted(accepted)
    diagnostics["fresh_required_count"] = len(requested - set(accepted))
    diagnostics["rejected_by_reason"] = {
        reason: sorted(values - set(accepted))
        for reason, values in sorted(rejected.items())
        if values - set(accepted)
    }
    return accepted, diagnostics


def prime_attested_resume_manifests_with_current_revalidation(
    *,
    root: Path,
    paper_dir: Path,
    import_module: str,
    semantic_dependency_modules: tuple[str, ...],
    current_context: Mapping[str, Any],
    current_bindings: Mapping[str, Mapping[str, Any]],
    resume_records: Mapping[str, Mapping[str, Any]],
    timeout_seconds: int = 300,
    revalidate: Callable[..., Mapping[str, Mapping[str, Any]]] = (
        run_lean_signature_manifest_revalidations
    ),
    reattach: Callable[..., dict[str, dict[str, Any]]] = (
        reattach_semantic_dependency_module_identities
    ),
    seed: Callable[..., set[str]] = seed_lean_signature_manifest_context_cache,
) -> tuple[dict[str, dict[str, Any]], dict[str, Any]]:
    """Recover a checkpoint only through a carrier plus current Lean receipts.

    This is the interrupted-refresh fallback after exact-context attestation
    cannot seed any row.  A local checkpoint remains non-authoritative: it
    must carry the caller's exact current context digest and source binding,
    and its Lean-owned payload must equal a manifest already authenticated by
    the tracked authority/carrier pair.  A current compact Lean revalidation
    then has to reproduce the checkpoint's semantic graph before the carrier
    is rebound to current reached artifacts and seeded in memory.

    The checkpoint never supplies a seeded manifest, and this helper never
    publishes authority or carrier files.  Missing historical carrier evidence,
    any changed source coordinate, or any current Lean disagreement is a cache
    miss.
    """

    paper, authority_contexts, store_entries = _validated_store_entries(paper_dir)
    requested = {
        str(qualified).strip()
        for qualified in current_bindings
        if str(qualified).strip()
    }
    diagnostics: dict[str, Any] = {
        "schema": 1,
        "paper": paper_dir.name,
        "requested_count": len(requested),
        "candidate_count": 0,
        "item_revalidation_requested_count": 0,
        "item_revalidated_count": 0,
        "seeded_count": 0,
        "seeded_declarations": [],
        "fresh_required_count": len(requested),
        "rejected_by_reason": {},
        "store_status": "unavailable_empty_or_invalid",
    }
    if paper != paper_dir.name or not requested or not store_entries:
        return {}, diagnostics

    current_authority = _context_authority(current_context)
    current_context_sha = signature_manifest_cache_context_sha256(current_context)
    expected_modules = tuple(semantic_dependency_modules)
    if (
        current_authority is None
        or not _sha256(current_context_sha)
        or str(current_authority.get("import_module") or "").strip()
        != import_module
        or tuple(current_authority.get("semantic_dependency_modules") or ())
        != expected_modules
    ):
        diagnostics["store_status"] = "current_context_malformed"
        return {}, diagnostics

    rejected: dict[str, set[str]] = {}

    def reject(reason: str, qualified: str) -> None:
        rejected.setdefault(reason, set()).add(qualified)

    candidates: dict[
        str, tuple[Mapping[str, Any], Mapping[str, Any], Mapping[str, Any]]
    ] = {}
    for qualified in sorted(requested):
        current_binding = current_bindings.get(qualified)
        resume = resume_records.get(qualified)
        stored = store_entries.get(qualified)
        if not isinstance(current_binding, Mapping):
            reject("current_source_binding_malformed", qualified)
            continue
        if (
            not isinstance(resume, Mapping)
            or set(resume) != {
                "binding",
                "manifest",
                "manifest_cache_context_sha256",
            }
            or resume.get("manifest_cache_context_sha256") != current_context_sha
        ):
            reject("resume_context_or_record_malformed", qualified)
            continue
        resume_binding = resume.get("binding")
        resume_manifest = resume.get("manifest")
        if not isinstance(resume_binding, Mapping) or dict(resume_binding) != dict(
            current_binding
        ):
            reject("resume_binding_changed", qualified)
            continue
        if stored is None:
            reject("authenticated_manifest_missing", qualified)
            continue
        authority_entry, carrier_manifest = stored
        prior_context = authority_contexts.get(
            str(authority_entry.get("context_id") or "").strip()
        )
        if (
            not isinstance(prior_context, Mapping)
            or str(prior_context.get("import_module") or "").strip()
            != import_module
            or tuple(prior_context.get("semantic_dependency_modules") or ())
            != expected_modules
        ):
            reject("authenticated_manifest_scope_changed", qualified)
            continue
        if (
            carrier_manifest.get("canonical_representation")
            != current_context.get("canonical_representation")
            or portable_semantic_hash_tool_identity(
                carrier_manifest.get("semantic_hash_tool_identity")
            )
            != portable_semantic_hash_tool_identity(
                current_context.get("semantic_hash_tool_identity")
            )
        ):
            reject("authenticated_manifest_context_identity_changed", qualified)
            continue
        if not _resume_lean_payload_matches_carrier(
            resume_manifest, carrier_manifest, authority_entry
        ):
            reject("resume_payload_not_attested", qualified)
            continue
        candidates[qualified] = (resume_manifest, carrier_manifest, authority_entry)

    diagnostics["candidate_count"] = len(candidates)
    diagnostics["item_revalidation_requested_count"] = len(candidates)
    if not candidates:
        diagnostics["store_status"] = "validated_recovery_no_candidates"
        diagnostics["rejected_by_reason"] = {
            reason: sorted(values)
            for reason, values in sorted(rejected.items())
            if values
        }
        return {}, diagnostics

    try:
        receipts = revalidate(
            root,
            import_module,
            sorted(candidates),
            timeout_seconds=timeout_seconds,
            build_timeout_seconds=timeout_seconds,
            semantic_dependency_modules=expected_modules,
            current_context=current_context,
        )
    except Exception:  # noqa: BLE001 - a cache optimization must fail closed.
        receipts = {}
    if not isinstance(receipts, Mapping):
        receipts = {}

    current_candidates: dict[str, dict[str, Any]] = {}
    revalidated: set[str] = set()
    for qualified, (resume_manifest, carrier_manifest, _authority_entry) in (
        candidates.items()
    ):
        receipt = receipts.get(qualified)
        if not isinstance(receipt, Mapping):
            reject("manifest_item_revalidation_unavailable", qualified)
            continue
        # The cache file's context digest was checked above, so the same
        # current context is both the checkpoint context and the environment
        # whose compact Lean receipt is being verified here.
        if not signature_manifest_item_revalidation_matches(
            resume_manifest,
            receipt,
            declaration=qualified,
            prior_context=current_context,
            current_context=current_context,
        ):
            reject("manifest_item_semantics_changed", qualified)
            continue
        current_candidates[qualified] = {
            **carrier_manifest,
            "semantic_dependency_graph": dict(receipt["semantic_dependency_graph"]),
            "elaborated_execution_state_refinement_shape": dict(
                receipt["elaborated_execution_state_refinement_shape"]
            ),
        }
        revalidated.add(qualified)

    try:
        rebound = reattach(root, current_candidates, timeout_seconds=timeout_seconds)
    except Exception:  # noqa: BLE001 - a cache optimization must fail closed.
        rebound = {}
    if not isinstance(rebound, Mapping):
        rebound = {}

    accepted_candidates: dict[str, dict[str, Any]] = {}
    pins: dict[str, dict[str, str]] = {}
    for qualified in sorted(current_candidates):
        current_manifest = rebound.get(qualified)
        candidate = candidates.get(qualified)
        if not isinstance(current_manifest, Mapping) or candidate is None:
            reject("current_dependency_artifacts_unavailable", qualified)
            continue
        _resume_manifest, _carrier_manifest, authority_entry = candidate
        dependency = semantic_dependency_manifest(current_manifest)
        signature = _sha256(authority_entry.get("elaborated_signature_sha256"))
        graph = _sha256(authority_entry.get("elaborated_proposition_graph_sha256"))
        dependency_sha = (
            _sha256(dependency.get("semantic_dependency_sha256"))
            if isinstance(dependency, Mapping)
            else ""
        )
        if (
            signature_manifest_digest(dict(current_manifest)) != signature
            or elaborated_proposition_graph_sha256(
                current_manifest.get("elaborated_proposition_graph")
            )
            != graph
            or not dependency_sha
        ):
            reject("current_manifest_identity_changed", qualified)
            continue
        manifest = dict(current_manifest)
        manifest["semantic_dependency_manifest"] = dict(dependency)
        accepted_candidates[qualified] = manifest
        pins[qualified] = {
            "manifest_cache_context_sha256": current_context_sha,
            "elaborated_signature_sha256": signature,
            "semantic_dependency_sha256": dependency_sha,
        }

    accepted: dict[str, dict[str, Any]] = {}
    if accepted_candidates:
        try:
            seeded = seed(
                root,
                import_module,
                accepted_candidates,
                pins,
                semantic_dependency_modules=expected_modules,
                current_context=current_context,
            )
        except Exception:  # noqa: BLE001 - a cache optimization must fail closed.
            seeded = set()
        for qualified in seeded:
            manifest = accepted_candidates.get(qualified)
            if manifest is not None:
                accepted[qualified] = manifest
        for qualified in set(accepted_candidates) - set(seeded):
            reject("context_cache_seed_rejected", qualified)

    diagnostics["store_status"] = "validated_current_recovery_revalidation"
    diagnostics["item_revalidated_count"] = len(revalidated & set(accepted))
    diagnostics["seeded_count"] = len(accepted)
    diagnostics["seeded_declarations"] = sorted(accepted)
    diagnostics["fresh_required_count"] = len(requested - set(accepted))
    diagnostics["rejected_by_reason"] = {
        reason: sorted(values - set(accepted))
        for reason, values in sorted(rejected.items())
        if values - set(accepted)
    }
    return accepted, diagnostics


def prime_authenticated_manifest_store_with_item_revalidation(
    *,
    root: Path,
    paper_dir: Path,
    authenticated_prior_rows: Iterable[Mapping[str, Any]],
    current_declarations: Mapping[str, Mapping[str, Any]],
    prior_contexts: Iterable[Mapping[str, Any]],
    current_contexts: Iterable[Mapping[str, Any]],
    timeout_seconds: int = 300,
    revalidate: Callable[..., Mapping[str, Mapping[str, Any]]] = (
        run_lean_signature_manifest_revalidations
    ),
    reattach: Callable[..., dict[str, dict[str, Any]]] = (
        reattach_semantic_dependency_module_identities
    ),
    seed: Callable[..., set[str]] = seed_lean_signature_manifest_context_cache,
) -> tuple[dict[str, dict[str, Any]], dict[str, Any]]:
    """Revalidate authenticated manifests one unchanged declaration at a time.

    This is the context-change fallback for callers that independently
    authenticated a prior source-record row.  The tracked authority and ignored
    carrier authenticate the complete prior manifest; the prior raw row
    independently authenticates its signature, dependency, proposition graph,
    exact declaration text, and source coordinate.  A current exact declaration
    match plus Lean's compact graph receipt may then retain that manifest after
    an unrelated module-level artifact change.

    Declaration names are lookup coordinates only.  A missing, duplicate, or
    contradictory coordinate is a cache miss, as is any changed declaration
    byte.  This helper does not validate the prior raw receipt itself; callers
    must do so before supplying ``authenticated_prior_rows``.
    """

    paper, authority_contexts, store_entries = _validated_store_entries(paper_dir)
    requested = {
        str(qualified).strip()
        for qualified in current_declarations
        if str(qualified).strip()
    }
    diagnostics: dict[str, Any] = {
        "schema": 1,
        "paper": paper_dir.name,
        "requested_count": len(requested),
        "candidate_count": len(store_entries),
        "exact_context_candidate_count": 0,
        "item_revalidation_requested_count": 0,
        "item_revalidated_count": 0,
        "seeded_count": 0,
        "seeded_declarations": [],
        "fresh_required_count": len(requested),
        "rejected_by_reason": {},
    }
    if paper != paper_dir.name or not requested or not store_entries:
        diagnostics["store_status"] = "unavailable_empty_or_invalid"
        return {}, diagnostics

    rejected: dict[str, set[str]] = {}

    def reject(reason: str, declarations: Iterable[str]) -> None:
        rejected.setdefault(reason, set()).update(
            declaration for declaration in declarations if declaration
        )

    prior_rows: dict[str, Mapping[str, Any]] = {}
    duplicate_prior_rows: set[str] = set()
    for raw_row in authenticated_prior_rows:
        if not isinstance(raw_row, Mapping):
            continue
        qualified = str(raw_row.get("qualified_declaration") or "").strip()
        if not qualified or qualified in duplicate_prior_rows:
            continue
        if qualified in prior_rows:
            prior_rows.pop(qualified, None)
            duplicate_prior_rows.add(qualified)
            continue
        prior_rows[qualified] = raw_row

    def contexts_by_module(
        values: Iterable[Mapping[str, Any]],
    ) -> tuple[dict[str, Mapping[str, Any]], set[str]]:
        indexed: dict[str, Mapping[str, Any]] = {}
        ambiguous: set[str] = set()
        for value in values:
            if not isinstance(value, Mapping):
                continue
            module = str(value.get("import_module") or "").strip()
            if not module or not signature_manifest_cache_context_sha256(value):
                continue
            if module in ambiguous:
                continue
            prior = indexed.get(module)
            if prior is not None and dict(prior) != dict(value):
                indexed.pop(module, None)
                ambiguous.add(module)
            elif prior is None:
                indexed[module] = value
        return indexed, ambiguous

    prior_context_by_module, ambiguous_prior_contexts = contexts_by_module(
        prior_contexts
    )
    current_context_by_module, ambiguous_current_contexts = contexts_by_module(
        current_contexts
    )

    candidates: dict[str, dict[str, Any]] = {}
    candidate_contexts: dict[str, Mapping[str, Any]] = {}
    candidate_modules: dict[str, tuple[str, ...]] = {}
    item_revalidation_candidates: dict[
        str,
        tuple[
            dict[str, Any],
            Mapping[str, Any],
            Mapping[str, Any],
            str,
            tuple[str, ...],
        ],
    ] = {}

    for qualified in sorted(requested):
        if qualified in duplicate_prior_rows:
            reject("ambiguous_prior_raw_row", [qualified])
            continue
        prior_row = prior_rows.get(qualified)
        current = current_declarations.get(qualified)
        stored = store_entries.get(qualified)
        if prior_row is None:
            reject("prior_raw_row_missing", [qualified])
            continue
        if not isinstance(current, Mapping):
            reject("current_declaration_missing", [qualified])
            continue
        if stored is None:
            reject("authenticated_manifest_missing", [qualified])
            continue
        authority_entry, manifest = stored
        prior_source = str(prior_row.get("lean_source_declaration") or "")
        current_source = str(current.get("lean_source_declaration") or "")
        prior_source_file = str(prior_row.get("source_file") or "").replace(
            "\\", "/"
        ).strip()
        current_source_file = str(current.get("source_file") or "").replace(
            "\\", "/"
        ).strip()
        if not prior_source or current_source != prior_source:
            reject("declaration_source_changed", [qualified])
            continue
        if not prior_source_file or current_source_file != prior_source_file:
            reject("declaration_source_coordinate_changed", [qualified])
            continue

        prior_signature = _sha256(
            prior_row.get("elaborated_signature_sha256")
        )
        prior_dependency = _sha256(
            prior_row.get("semantic_dependency_sha256")
        )
        prior_graph = configured_review_row_proposition_graph_sha256(prior_row)
        if (
            prior_signature != authority_entry["elaborated_signature_sha256"]
            or prior_dependency != authority_entry["semantic_dependency_sha256"]
            or prior_graph
            != authority_entry["elaborated_proposition_graph_sha256"]
        ):
            reject("prior_raw_manifest_identity_mismatch", [qualified])
            continue

        authority_context = authority_contexts.get(authority_entry["context_id"])
        if not isinstance(authority_context, Mapping):
            reject("authenticated_context_missing", [qualified])
            continue
        import_module = str(authority_context.get("import_module") or "").strip()
        modules = tuple(authority_context.get("semantic_dependency_modules") or ())
        if (
            not import_module
            or import_module in ambiguous_prior_contexts
            or import_module in ambiguous_current_contexts
        ):
            reject("ambiguous_manifest_context", [qualified])
            continue
        prior_context = prior_context_by_module.get(import_module)
        current_context = current_context_by_module.get(import_module)
        if not isinstance(prior_context, Mapping):
            reject("prior_manifest_context_missing", [qualified])
            continue
        if (
            signature_manifest_cache_context_sha256(prior_context)
            != authority_context["manifest_cache_context_sha256"]
        ):
            reject("prior_manifest_context_not_authenticated", [qualified])
            continue
        if not isinstance(current_context, Mapping):
            reject("current_manifest_context_missing", [qualified])
            continue
        if (
            str(current_context.get("import_module") or "").strip()
            != import_module
            or tuple(current_context.get("audit_modules") or ()) != modules
        ):
            reject("current_manifest_scope_changed", [qualified])
            continue

        current_context_sha256 = signature_manifest_cache_context_sha256(
            current_context
        )
        if (
            current_context_sha256
            == authority_context["manifest_cache_context_sha256"]
        ):
            candidates[qualified] = dict(manifest)
            candidate_contexts[qualified] = current_context
            candidate_modules[qualified] = modules
            continue
        item_revalidation_candidates[qualified] = (
            dict(manifest),
            prior_context,
            current_context,
            import_module,
            modules,
        )

    diagnostics["exact_context_candidate_count"] = len(candidates)
    diagnostics["item_revalidation_requested_count"] = len(
        item_revalidation_candidates
    )
    revalidation_groups: dict[
        tuple[str, str],
        tuple[str, tuple[str, ...], Mapping[str, Any], list[str]],
    ] = {}
    for qualified, details in item_revalidation_candidates.items():
        _manifest, _prior_context, current_context, import_module, modules = details
        context_digest = signature_manifest_cache_context_sha256(current_context)
        key = (import_module, context_digest)
        group = revalidation_groups.get(key)
        if group is None:
            revalidation_groups[key] = (
                import_module,
                modules,
                current_context,
                [qualified],
            )
        elif group[1] == modules and dict(group[2]) == dict(current_context):
            group[3].append(qualified)
        else:
            reject("ambiguous_current_manifest_context", [qualified])

    item_revalidated: set[str] = set()
    for import_module, modules, current_context, qualified_names in (
        revalidation_groups.values()
    ):
        try:
            receipts = revalidate(
                root,
                import_module,
                qualified_names,
                timeout_seconds=timeout_seconds,
                build_timeout_seconds=timeout_seconds,
                semantic_dependency_modules=modules,
                current_context=current_context,
            )
        except Exception:  # noqa: BLE001 - failed optimization remains a miss.
            receipts = {}
        if not isinstance(receipts, Mapping):
            receipts = {}
        for qualified in qualified_names:
            manifest, prior_context, candidate_context, _module, modules = (
                item_revalidation_candidates[qualified]
            )
            receipt = receipts.get(qualified)
            if not isinstance(receipt, Mapping):
                reject("manifest_item_revalidation_unavailable", [qualified])
                continue
            if not signature_manifest_item_revalidation_matches(
                manifest,
                receipt,
                declaration=qualified,
                prior_context=prior_context,
                current_context=candidate_context,
            ):
                reject("manifest_item_semantics_changed", [qualified])
                continue
            candidates[qualified] = {
                **manifest,
                "semantic_dependency_graph": dict(
                    receipt["semantic_dependency_graph"]
                ),
                "elaborated_execution_state_refinement_shape": dict(
                    receipt["elaborated_execution_state_refinement_shape"]
                ),
            }
            candidate_contexts[qualified] = candidate_context
            candidate_modules[qualified] = modules
            item_revalidated.add(qualified)

    try:
        rebound = reattach(root, candidates, timeout_seconds=timeout_seconds)
    except Exception:  # noqa: BLE001 - a cache optimization must fail closed.
        rebound = {}
    if not isinstance(rebound, Mapping):
        rebound = {}

    seed_groups: dict[
        tuple[str, str],
        tuple[Mapping[str, Any], tuple[str, ...], dict[str, dict[str, Any]]],
    ] = {}
    for qualified in sorted(candidates):
        current_manifest = rebound.get(qualified)
        stored = store_entries.get(qualified)
        current_context = candidate_contexts.get(qualified)
        modules = candidate_modules.get(qualified)
        if (
            not isinstance(current_manifest, Mapping)
            or stored is None
            or not isinstance(current_context, Mapping)
            or not isinstance(modules, tuple)
        ):
            reject("current_dependency_artifacts_unavailable", [qualified])
            continue
        authority_entry = stored[0]
        dependency = semantic_dependency_manifest(current_manifest)
        if (
            signature_manifest_digest(current_manifest)
            != authority_entry["elaborated_signature_sha256"]
            or not isinstance(dependency, Mapping)
            or _sha256(dependency.get("semantic_dependency_sha256"))
            != authority_entry["semantic_dependency_sha256"]
            or elaborated_proposition_graph_sha256(
                current_manifest.get("elaborated_proposition_graph")
            )
            != authority_entry["elaborated_proposition_graph_sha256"]
        ):
            reject("current_manifest_identity_changed", [qualified])
            continue
        import_module = str(current_context.get("import_module") or "").strip()
        context_digest = signature_manifest_cache_context_sha256(current_context)
        group_key = (import_module, context_digest)
        group = seed_groups.get(group_key)
        if group is None:
            seed_groups[group_key] = (current_context, modules, {})
            group = seed_groups[group_key]
        group[2][qualified] = dict(current_manifest)

    accepted: dict[str, dict[str, Any]] = {}
    for current_context, modules, manifests in seed_groups.values():
        pins = {
            qualified: {
                "manifest_cache_context_sha256": (
                    signature_manifest_cache_context_sha256(current_context)
                ),
                "elaborated_signature_sha256": store_entries[qualified][0][
                    "elaborated_signature_sha256"
                ],
                "semantic_dependency_sha256": store_entries[qualified][0][
                    "semantic_dependency_sha256"
                ],
            }
            for qualified in manifests
        }
        try:
            seeded = seed(
                root,
                str(current_context.get("import_module") or ""),
                manifests,
                pins,
                build_timeout_seconds=timeout_seconds,
                semantic_dependency_modules=modules,
                current_context=current_context,
            )
        except Exception:  # noqa: BLE001 - a seed rejection remains a miss.
            seeded = set()
        rejected_seed = set(manifests) - set(seeded)
        reject("context_cache_seed_rejected", rejected_seed)
        for qualified in seeded:
            manifest = manifests.get(qualified)
            if manifest is not None:
                accepted[qualified] = manifest

    diagnostics["store_status"] = "validated_with_item_revalidation"
    diagnostics["item_revalidated_count"] = len(item_revalidated & set(accepted))
    diagnostics["seeded_count"] = len(accepted)
    diagnostics["seeded_declarations"] = sorted(accepted)
    diagnostics["fresh_required_count"] = len(requested - set(accepted))
    diagnostics["rejected_by_reason"] = {
        reason: sorted(declarations - set(accepted))
        for reason, declarations in sorted(rejected.items())
        if declarations - set(accepted)
    }
    return accepted, diagnostics


def _legacy_context_key(
    source_file: str, contexts: Mapping[str, Any]
) -> str:
    normalized = source_file.replace("\\", "/").strip()
    matches = [
        str(key)
        for key in contexts
        if normalized == str(key) or normalized.endswith("/" + str(key))
    ]
    return matches[0] if len(matches) == 1 else ""


def migrate_legacy_schema20_manifest_store(
    *,
    paper_dir: Path,
    paper: str,
    validated_configured_rows: Iterable[Mapping[str, Any]],
    legacy_cache: Mapping[str, Any] | None = None,
) -> set[str]:
    """Import only schema-20 rows exactly attested by canonical raw rows.

    ``validated_configured_rows`` must come from an independently receipt-
    validated canonical source-record audit.  Names only join exact qualified
    coordinates; every mathematical and context identity is compared below.
    """

    cache = (
        dict(legacy_cache)
        if isinstance(legacy_cache, Mapping)
        else _load_json(paper_dir / ".review_traces" / "paper_interface_cache.json")
    )
    rows = cache.get("rows")
    contexts = cache.get("signature_contexts")
    if (
        cache.get("schema") != LEGACY_PAPER_INTERFACE_CACHE_SCHEMA
        or cache.get("paper") != paper
        or not isinstance(rows, list)
        or not isinstance(contexts, Mapping)
    ):
        return set()
    legacy_by_qualified: dict[str, Mapping[str, Any]] = {}
    duplicates: set[str] = set()
    for raw_row in rows:
        if not isinstance(raw_row, Mapping):
            continue
        qualified = str(raw_row.get("full_name") or "").strip()
        if not qualified:
            continue
        if qualified in legacy_by_qualified:
            duplicates.add(qualified)
        else:
            legacy_by_qualified[qualified] = raw_row

    candidates: list[dict[str, Any]] = []
    seen_authority: set[str] = set()
    for authority_row in validated_configured_rows:
        if not isinstance(authority_row, Mapping):
            continue
        qualified = str(
            authority_row.get("qualified_declaration") or ""
        ).strip()
        if not qualified or qualified in seen_authority:
            duplicates.add(qualified)
            continue
        seen_authority.add(qualified)
        legacy_row = legacy_by_qualified.get(qualified)
        manifest = legacy_row.get("lean_signature_manifest") if legacy_row else None
        context_key = _legacy_context_key(
            str(authority_row.get("source_file") or ""), contexts
        )
        context = contexts.get(context_key) if context_key else None
        signature = _sha256(authority_row.get("elaborated_signature_sha256"))
        dependency_sha256 = _sha256(
            authority_row.get("semantic_dependency_sha256")
        )
        proposition_graph_sha256 = configured_review_row_proposition_graph_sha256(
            authority_row
        )
        manifest_proposition_graph_sha256 = (
            elaborated_proposition_graph_sha256(
                manifest.get("elaborated_proposition_graph")
            )
            if isinstance(manifest, Mapping)
            else ""
        )
        if (
            qualified in duplicates
            or not isinstance(legacy_row, Mapping)
            or not isinstance(manifest, Mapping)
            or not isinstance(context, Mapping)
            or not signature
            or not dependency_sha256
            or not proposition_graph_sha256
            or _sha256(legacy_row.get("lean_signature_sha256")) != signature
            or signature_manifest_digest(manifest) != signature
            or manifest_proposition_graph_sha256 != proposition_graph_sha256
        ):
            continue
        dependency = semantic_dependency_manifest(manifest)
        if (
            not isinstance(dependency, Mapping)
            or _sha256(dependency.get("semantic_dependency_sha256"))
            != dependency_sha256
        ):
            continue
        binding = {
            key: authority_row.get(key)
            for key in (
                "qualified_declaration",
                "lean_source_declaration",
                "effective_qualified_declaration",
                "effective_lean_source_declaration",
                "review_alias_expansion",
                "source_file",
                "source_sha256",
                "elaborated_signature_sha256",
                "semantic_dependency_sha256",
            )
        }
        binding["elaborated_proposition_graph_sha256"] = (
            proposition_graph_sha256
        )
        candidates.append(
            {
                "qualified_declaration": qualified,
                "manifest": manifest,
                "context": context,
                "authority_binding": binding,
            }
        )
    if duplicates:
        candidates = [
            candidate
            for candidate in candidates
            if candidate["qualified_declaration"] not in duplicates
        ]
    if not candidates:
        return set()
    return publish_authenticated_manifest_store(
        paper_dir=paper_dir,
        paper=paper,
        candidates=candidates,
    )
