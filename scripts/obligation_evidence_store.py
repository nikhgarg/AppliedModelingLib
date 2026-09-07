#!/usr/bin/env python3
"""Portable per-paper persistence for independently authenticated leaves.

Leaf objects are written before the small graph index.  A failed producer or
late graph-validation error therefore cannot erase earlier successful work.
Store presence alone never grants acceptance. Only the selected accepted graph,
after exact terminal-issuance and current-control validation, is the paper's
acceptance credential. Its packed form is a transport, not a second authority.
"""

from __future__ import annotations

import hashlib
import json
import os
import re
import tempfile
from collections.abc import Iterable, Mapping
from dataclasses import dataclass
from pathlib import Path
from types import MappingProxyType
from typing import Any

try:
    from scripts.accepted_obligation_graph import (
        AcceptedObligationGraphCredential,
        AcceptedObligationGraphError,
        build_accepted_obligation_graph,
        validate_accepted_obligation_graph,
    )
    from scripts.obligation_evidence_graph import (
        ObligationEvidenceError,
        ObligationEvidenceGraph,
        ObligationEvidenceLeaf,
        build_obligation_graph,
        validate_obligation_graph,
        validate_obligation_leaf,
    )
    from scripts.obligation_evidence_issuance import (
        ObligationEvidenceIssuance,
        ObligationEvidenceIssuanceError,
        validate_obligation_evidence_issuance,
    )
    from scripts.obligation_paper_bundle import (
        PaperObligationBundle,
        PaperObligationBundleError,
        build_accepting_paper_obligation_bundle,
        build_paper_obligation_bundle,
        validate_paper_obligation_bundle,
    )
    from scripts.obligation_paper_index import (
        PaperObligationIndex,
        PaperObligationIndexError,
        validate_paper_obligation_index,
    )
    from scripts.obligation_preflight import ObligationStructuralPreflight
    from scripts.lean_import_closure import (
        lean_import_closure_payload_sha256,
        validated_lean_import_closure_payload,
    )
    from scripts.portable_evidence_identity import canonical_json_bytes
    from scripts.strict_closeout_authority import StrictCloseoutAuthority
except ModuleNotFoundError:  # Direct ``python scripts/...`` execution.
    from accepted_obligation_graph import (
        AcceptedObligationGraphCredential,
        AcceptedObligationGraphError,
        build_accepted_obligation_graph,
        validate_accepted_obligation_graph,
    )
    from obligation_evidence_graph import (
        ObligationEvidenceError,
        ObligationEvidenceGraph,
        ObligationEvidenceLeaf,
        build_obligation_graph,
        validate_obligation_graph,
        validate_obligation_leaf,
    )
    from obligation_evidence_issuance import (
        ObligationEvidenceIssuance,
        ObligationEvidenceIssuanceError,
        validate_obligation_evidence_issuance,
    )
    from obligation_paper_bundle import (
        PaperObligationBundle,
        PaperObligationBundleError,
        build_accepting_paper_obligation_bundle,
        build_paper_obligation_bundle,
        validate_paper_obligation_bundle,
    )
    from obligation_paper_index import (
        PaperObligationIndex,
        PaperObligationIndexError,
        validate_paper_obligation_index,
    )
    from obligation_preflight import ObligationStructuralPreflight
    from lean_import_closure import (
        lean_import_closure_payload_sha256,
        validated_lean_import_closure_payload,
    )
    from portable_evidence_identity import canonical_json_bytes
    from strict_closeout_authority import StrictCloseoutAuthority


PAPER_RE = re.compile(r"^[A-Za-z0-9][A-Za-z0-9_.-]*$")
SHA256_RE = re.compile(r"^[0-9a-f]{64}$")
EVIDENCE_DIRECTORY = Path("audit") / "obligation_evidence"
LEAF_DIRECTORY = EVIDENCE_DIRECTORY / "sha256"
ISSUANCE_BY_LEAF_DIRECTORY = EVIDENCE_DIRECTORY / "attestations" / "by_leaf"
GRAPH_INDEX_NAME = "obligation_evidence_graph.json"
GRAPH_OBJECT_DIRECTORY = EVIDENCE_DIRECTORY / "graphs" / "sha256"
PAPER_INDEX_DIRECTORY = EVIDENCE_DIRECTORY / "paper_indexes" / "sha256"
BUNDLE_DIRECTORY = EVIDENCE_DIRECTORY / "bundles" / "sha256"
CURRENT_BUNDLE_NAME = "current_bundle.json"
CURRENT_ACCEPTED_GRAPH_NAME = "current_accepted_graph.json"
ACCEPTED_GRAPH_PACK_DIRECTORY = (
    EVIDENCE_DIRECTORY / "accepted_graphs" / "sha256"
)
PACKED_ACCEPTED_GRAPH_SCHEMA = 1
PACKED_ACCEPTED_GRAPH_POINTER_SCHEMA = 2
LEAN_RESOLUTION_DIRECTORY = EVIDENCE_DIRECTORY / "lean_resolutions" / "sha256"
LEAN_IMPORT_CLOSURE_DIRECTORY = (
    EVIDENCE_DIRECTORY / "lean_import_closures" / "sha256"
)


class ObligationEvidenceStoreError(ValueError):
    """The portable evidence store is unsafe, corrupt, or incomplete."""


@dataclass(frozen=True)
class LoadedPaperObligationBundle:
    """Authenticated current bundle and the exact objects it selects."""

    bundle: PaperObligationBundle
    paper_index: PaperObligationIndex
    graph: ObligationEvidenceGraph
    issuances: Mapping[str, ObligationEvidenceIssuance]


@dataclass(frozen=True)
class ObligationEvidenceStoreSnapshot:
    """Exact required-leaf lookup for the pure planner, including corruption."""

    available_leaves: Mapping[str, object]
    issuances: tuple[Mapping[str, Any], ...]


@dataclass(frozen=True)
class LoadedLeanDeclarationResolution:
    """Authenticated restart carrier, still pending current-context validation."""

    leaf: ObligationEvidenceLeaf
    issuance: ObligationEvidenceIssuance
    manifest_cache_context_sha256: str
    manifest_revalidation_basis: Mapping[str, Any]


def _paper_folder(root: Path, paper: str) -> Path:
    paper = str(paper).strip()
    if not PAPER_RE.fullmatch(paper):
        raise ObligationEvidenceStoreError("paper name is invalid")
    root = root.resolve()
    folder = (root / "papers" / paper).resolve()
    try:
        folder.relative_to(root)
    except ValueError as exc:
        raise ObligationEvidenceStoreError("paper folder escapes the repository") from exc
    return folder


def _leaf_path(root: Path, paper: str, digest: str) -> Path:
    digest = str(digest).strip().lower()
    if not SHA256_RE.fullmatch(digest):
        raise ObligationEvidenceStoreError("leaf identity is not SHA-256")
    return _paper_folder(root, paper) / LEAF_DIRECTORY / digest[:2] / f"{digest}.json"


def graph_index_path(root: Path, paper: str) -> Path:
    return _paper_folder(root, paper) / EVIDENCE_DIRECTORY / GRAPH_INDEX_NAME


def _issuance_by_leaf_path(
    root: Path,
    paper: str,
    leaf_sha256: str,
    issuance_sha256: str,
) -> Path:
    leaf_sha256 = str(leaf_sha256).strip().lower()
    issuance_sha256 = str(issuance_sha256).strip().lower()
    if not SHA256_RE.fullmatch(leaf_sha256) or not SHA256_RE.fullmatch(
        issuance_sha256
    ):
        raise ObligationEvidenceStoreError(
            "leaf issuance index contains a malformed identity"
        )
    return (
        _paper_folder(root, paper)
        / ISSUANCE_BY_LEAF_DIRECTORY
        / leaf_sha256[:2]
        / leaf_sha256
        / f"{issuance_sha256}.json"
    )


def _content_object_path(
    root: Path,
    paper: str,
    directory: Path,
    digest: str,
) -> Path:
    digest = str(digest).strip().lower()
    if not SHA256_RE.fullmatch(digest):
        raise ObligationEvidenceStoreError("object identity is not SHA-256")
    return _paper_folder(root, paper) / directory / digest[:2] / f"{digest}.json"


def _graph_object_path(root: Path, paper: str, digest: str) -> Path:
    return _content_object_path(root, paper, GRAPH_OBJECT_DIRECTORY, digest)


def _paper_index_path(root: Path, paper: str, digest: str) -> Path:
    return _content_object_path(root, paper, PAPER_INDEX_DIRECTORY, digest)


def _bundle_path(root: Path, paper: str, digest: str) -> Path:
    return _content_object_path(root, paper, BUNDLE_DIRECTORY, digest)


def _accepted_graph_pack_path(root: Path, paper: str, digest: str) -> Path:
    return _content_object_path(
        root,
        paper,
        ACCEPTED_GRAPH_PACK_DIRECTORY,
        digest,
    )


def _lean_import_closure_path(root: Path, paper: str, digest: str) -> Path:
    return _content_object_path(
        root,
        paper,
        LEAN_IMPORT_CLOSURE_DIRECTORY,
        digest,
    )


def current_bundle_path(root: Path, paper: str) -> Path:
    return _paper_folder(root, paper) / EVIDENCE_DIRECTORY / CURRENT_BUNDLE_NAME


def current_accepted_graph_path(root: Path, paper: str) -> Path:
    """Return the sole canonical acceptance pointer for new closeouts."""

    return (
        _paper_folder(root, paper)
        / EVIDENCE_DIRECTORY
        / CURRENT_ACCEPTED_GRAPH_NAME
    )


def lean_declaration_resolution_directory(
    root: Path, paper: str, coordinate_sha256: str
) -> Path:
    """Return the non-authoritative routing directory for one Lean coordinate."""

    digest = str(coordinate_sha256 or "").strip().lower()
    if not SHA256_RE.fullmatch(digest):
        raise ObligationEvidenceStoreError(
            "Lean declaration resolution coordinate is not SHA-256"
        )
    return _paper_folder(root, paper) / LEAN_RESOLUTION_DIRECTORY / digest


def _encoded(value: object) -> bytes:
    return canonical_json_bytes(value) + b"\n"


def _atomic_write(path: Path, payload: bytes) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    descriptor, raw_temp = tempfile.mkstemp(
        prefix=f".{path.name}.", suffix=".tmp", dir=path.parent
    )
    temporary = Path(raw_temp)
    try:
        with os.fdopen(descriptor, "wb") as stream:
            stream.write(payload)
            stream.flush()
            os.fsync(stream.fileno())
        os.replace(temporary, path)
    finally:
        try:
            temporary.unlink()
        except FileNotFoundError:
            pass


def _store_immutable_object(path: Path, value: Mapping[str, Any], label: str) -> Path:
    payload = _encoded(value)
    try:
        existing = path.read_bytes()
    except FileNotFoundError:
        _atomic_write(path, payload)
    except OSError as exc:
        raise ObligationEvidenceStoreError(f"could not read {label}: {exc}") from exc
    else:
        if existing != payload:
            raise ObligationEvidenceStoreError(
                f"content-addressed {label} contains conflicting bytes"
            )
    return path


def store_lean_import_closure_preimage(
    root: Path,
    paper: str,
    closure_sha256: str,
    value: Mapping[str, Any],
) -> Path:
    """Retain a non-credential closure preimage under its authenticated digest."""

    digest = str(closure_sha256 or "").strip().lower()
    if not SHA256_RE.fullmatch(digest):
        raise ObligationEvidenceStoreError(
            "Lean import-closure preimage identity is not SHA-256"
        )
    try:
        closure = validated_lean_import_closure_payload(value)
    except ValueError as exc:
        raise ObligationEvidenceStoreError(
            "Lean import-closure preimage is invalid: " + str(exc)
        ) from exc
    if lean_import_closure_payload_sha256(closure) != digest:
        raise ObligationEvidenceStoreError(
            "Lean import-closure preimage disagrees with its selected identity"
        )
    return _store_immutable_object(
        _lean_import_closure_path(root, paper, digest),
        closure,
        "Lean import-closure preimage",
    )


def load_lean_import_closure_preimage(
    root: Path,
    paper: str,
    closure_sha256: str,
) -> Mapping[str, Any]:
    """Load a closure preimage; callers must authenticate its digest externally."""

    digest = str(closure_sha256 or "").strip().lower()
    path = _lean_import_closure_path(root, paper, digest)
    value = _load_json_object(path, "Lean import-closure preimage")
    try:
        closure = validated_lean_import_closure_payload(value)
    except ValueError as exc:
        raise ObligationEvidenceStoreError(
            "Lean import-closure preimage is invalid: " + str(exc)
        ) from exc
    if lean_import_closure_payload_sha256(closure) != digest:
        raise ObligationEvidenceStoreError(
            "Lean import-closure preimage disagrees with its selected identity"
        )
    return MappingProxyType(closure)


def store_lean_declaration_resolution(
    root: Path,
    paper: str,
    *,
    coordinate_sha256: str,
    declaration: str,
    leaf: ObligationEvidenceLeaf,
    issuance: ObligationEvidenceIssuance,
    manifest_cache_context_sha256: str,
    manifest_revalidation_basis: Mapping[str, Any],
) -> Path:
    """Persist a restart hint only after its leaf and issuance are durable."""

    name = str(declaration or "").strip()
    if not name:
        raise ObligationEvidenceStoreError(
            "Lean declaration resolution has no declaration route"
        )
    if issuance.leaf_sha256 != leaf.leaf_sha256:
        raise ObligationEvidenceStoreError(
            "Lean declaration resolution issuance names a different leaf"
        )
    context_sha256 = str(manifest_cache_context_sha256 or "").strip().lower()
    if not SHA256_RE.fullmatch(context_sha256):
        raise ObligationEvidenceStoreError(
            "Lean declaration resolution context is not SHA-256"
        )
    if not isinstance(manifest_revalidation_basis, Mapping):
        raise ObligationEvidenceStoreError(
            "Lean declaration resolution basis is not an object"
        )
    basis = dict(manifest_revalidation_basis)
    basis_sha256 = hashlib.sha256(canonical_json_bytes(basis)).hexdigest()
    store_issued_obligation_leaf(root, paper, leaf, issuance)
    path = (
        lean_declaration_resolution_directory(root, paper, coordinate_sha256)
        / f"{issuance.issuance_sha256}.json"
    )
    payload = {
        "schema": 1,
        "acceptance_credential": False,
        "coordinate_sha256": str(coordinate_sha256).strip().lower(),
        "declaration": name,
        "leaf_sha256": leaf.leaf_sha256,
        "issuance_sha256": issuance.issuance_sha256,
        "manifest_cache_context_sha256": context_sha256,
        "manifest_revalidation_basis": basis,
        "manifest_revalidation_basis_sha256": basis_sha256,
    }
    return _store_immutable_object(
        path,
        payload,
        "Lean declaration resolution",
    )


def load_lean_declaration_resolution(
    root: Path,
    paper: str,
    *,
    coordinate_sha256: str,
    declaration: str,
    authenticated_authority_sha256s: Iterable[str],
    assurance_contract_sha256: str,
) -> LoadedLeanDeclarationResolution | None:
    """Load one exact restart hint; a missing record is an ordinary cache miss."""

    directory = lean_declaration_resolution_directory(
        root, paper, coordinate_sha256
    )
    if not directory.is_dir():
        return None
    required = {
        "schema",
        "acceptance_credential",
        "coordinate_sha256",
        "declaration",
        "leaf_sha256",
        "issuance_sha256",
        "manifest_cache_context_sha256",
        "manifest_revalidation_basis",
        "manifest_revalidation_basis_sha256",
    }
    authorities = {
        str(value or "").strip().lower()
        for value in authenticated_authority_sha256s
        if SHA256_RE.fullmatch(str(value or "").strip().lower())
    }
    expected_assurance = str(assurance_contract_sha256 or "").strip().lower()
    if not SHA256_RE.fullmatch(expected_assurance):
        raise ObligationEvidenceStoreError(
            "Lean declaration resolution assurance is not SHA-256"
        )
    for path in sorted(directory.glob("*.json")):
        try:
            payload = _load_json_object(path, "Lean declaration resolution")
        except ObligationEvidenceStoreError:
            continue
        if (
            set(payload) != required
            or payload.get("schema") != 1
            or payload.get("acceptance_credential") is not False
            or payload.get("coordinate_sha256")
            != str(coordinate_sha256).strip().lower()
            or payload.get("declaration") != str(declaration).strip()
        ):
            continue
        leaf_sha256 = str(payload.get("leaf_sha256") or "").strip().lower()
        issuance_sha256 = str(payload.get("issuance_sha256") or "").strip().lower()
        context_sha256 = str(
            payload.get("manifest_cache_context_sha256") or ""
        ).strip().lower()
        raw_basis = payload.get("manifest_revalidation_basis")
        basis_sha256 = str(
            payload.get("manifest_revalidation_basis_sha256") or ""
        ).strip().lower()
        if (
            not SHA256_RE.fullmatch(leaf_sha256)
            or not SHA256_RE.fullmatch(issuance_sha256)
            or not SHA256_RE.fullmatch(context_sha256)
            or not isinstance(raw_basis, Mapping)
            or not SHA256_RE.fullmatch(basis_sha256)
            or hashlib.sha256(canonical_json_bytes(raw_basis)).hexdigest()
            != basis_sha256
            or path.stem != issuance_sha256
        ):
            continue
        try:
            leaf = load_obligation_leaf(root, paper, leaf_sha256)
            issuance = load_obligation_evidence_issuance(
                root, paper, leaf_sha256, issuance_sha256
            )
        except ObligationEvidenceStoreError:
            continue
        semantic = leaf.semantic_payload
        expected_record_sha256 = hashlib.sha256(
            canonical_json_bytes(
                {
                    "schema": 1,
                    "coordinate_sha256": str(coordinate_sha256).strip().lower(),
                    "leaf_sha256": leaf.leaf_sha256,
                    "elaborated_signature_sha256": semantic.get(
                        "elaborated_signature_sha256"
                    ),
                    "elaborated_proposition_graph_sha256": semantic.get(
                        "elaborated_proposition_graph_sha256"
                    ),
                    "semantic_dependency_sha256": semantic.get(
                        "semantic_dependency_sha256"
                    ),
                    "manifest_cache_context_sha256": context_sha256,
                    "manifest_revalidation_basis_sha256": basis_sha256,
                }
            )
        ).hexdigest()
        if (
            issuance.leaf_sha256 == leaf.leaf_sha256
            and issuance.authority_sha256 in authorities
            and issuance.assurance_contract_sha256 == expected_assurance
            and issuance.evidence_record_sha256 == expected_record_sha256
        ):
            return LoadedLeanDeclarationResolution(
                leaf=leaf,
                issuance=issuance,
                manifest_cache_context_sha256=context_sha256,
                manifest_revalidation_basis=MappingProxyType(dict(raw_basis)),
            )
    return None


def store_obligation_leaf(
    root: Path,
    paper: str,
    leaf: ObligationEvidenceLeaf | Mapping[str, object],
) -> Path:
    """Persist one canonical leaf immediately, never overwriting a conflict."""

    try:
        parsed = validate_obligation_leaf(
            leaf.projection() if isinstance(leaf, ObligationEvidenceLeaf) else leaf
        )
    except ObligationEvidenceError as exc:
        raise ObligationEvidenceStoreError(str(exc)) from exc
    path = _leaf_path(root, paper, parsed.leaf_sha256)
    payload = _encoded(parsed.projection())
    try:
        existing = path.read_bytes()
    except FileNotFoundError:
        _atomic_write(path, payload)
    except OSError as exc:
        raise ObligationEvidenceStoreError(f"could not read obligation leaf: {exc}") from exc
    else:
        if existing != payload:
            raise ObligationEvidenceStoreError(
                "semantic-addressed leaf path contains conflicting bytes"
            )
    return path


def load_obligation_leaf(root: Path, paper: str, digest: str) -> ObligationEvidenceLeaf:
    """Read and authenticate one leaf from its semantic-addressed path."""

    path = _leaf_path(root, paper, digest)
    try:
        raw = json.loads(path.read_bytes())
    except (OSError, UnicodeDecodeError, json.JSONDecodeError) as exc:
        raise ObligationEvidenceStoreError(f"obligation leaf is unavailable: {exc}") from exc
    try:
        leaf = validate_obligation_leaf(raw)
    except ObligationEvidenceError as exc:
        raise ObligationEvidenceStoreError(str(exc)) from exc
    if leaf.leaf_sha256 != str(digest).strip().lower():
        raise ObligationEvidenceStoreError(
            "obligation leaf is stored under the wrong semantic identity"
        )
    if _encoded(leaf.projection()) != path.read_bytes():
        raise ObligationEvidenceStoreError("obligation leaf is not canonical JSON")
    return leaf


def store_obligation_evidence_issuance(
    root: Path,
    paper: str,
    issuance: ObligationEvidenceIssuance | Mapping[str, Any],
) -> Path:
    """Persist provenance separately from the semantic leaf it authorizes."""

    try:
        parsed = validate_obligation_evidence_issuance(
            issuance.projection()
            if isinstance(issuance, ObligationEvidenceIssuance)
            else issuance
        )
    except ObligationEvidenceIssuanceError as exc:
        raise ObligationEvidenceStoreError(str(exc)) from exc
    projection = parsed.projection()
    # An issuance is meaningful only for the exact leaf it authenticates. Store
    # it once under that pair instead of maintaining a second global copy and a
    # second readable authority. The filename still binds the issuance's own
    # content identity, while the parent route binds its authenticated leaf.
    path = _issuance_by_leaf_path(
        root,
        paper,
        parsed.leaf_sha256,
        parsed.issuance_sha256,
    )
    return _store_immutable_object(path, projection, "leaf issuance")


def store_issued_obligation_leaf(
    root: Path,
    paper: str,
    leaf: ObligationEvidenceLeaf | Mapping[str, object],
    issuance: ObligationEvidenceIssuance | Mapping[str, Any],
) -> tuple[Path, Path]:
    """Publish a successful semantic fact before its separate provenance edge.

    Both objects are validated before either write. The leaf is deliberately
    written first: interruption before issuance publication leaves an exact
    `authenticate_existing_leaf` task and never loses completed semantic work.
    """

    try:
        parsed_leaf = validate_obligation_leaf(
            leaf.projection() if isinstance(leaf, ObligationEvidenceLeaf) else leaf
        )
    except ObligationEvidenceError as exc:
        raise ObligationEvidenceStoreError(str(exc)) from exc
    try:
        parsed_issuance = validate_obligation_evidence_issuance(
            issuance.projection()
            if isinstance(issuance, ObligationEvidenceIssuance)
            else issuance
        )
    except ObligationEvidenceIssuanceError as exc:
        raise ObligationEvidenceStoreError(str(exc)) from exc
    if parsed_issuance.leaf_sha256 != parsed_leaf.leaf_sha256:
        raise ObligationEvidenceStoreError(
            "issuance authenticates a different obligation leaf"
        )
    leaf_path = store_obligation_leaf(root, paper, parsed_leaf)
    issuance_path = store_obligation_evidence_issuance(
        root, paper, parsed_issuance
    )
    return leaf_path, issuance_path


def load_obligation_evidence_issuance(
    root: Path, paper: str, leaf_sha256: str, digest: str
) -> ObligationEvidenceIssuance:
    """Read one leaf-bound issuance without treating it as acceptance."""

    expected_leaf = str(leaf_sha256).strip().lower()
    path = _issuance_by_leaf_path(root, paper, expected_leaf, digest)
    try:
        raw = json.loads(path.read_bytes())
    except (OSError, UnicodeDecodeError, json.JSONDecodeError) as exc:
        raise ObligationEvidenceStoreError(
            f"obligation issuance is unavailable: {exc}"
        ) from exc
    try:
        issuance = validate_obligation_evidence_issuance(raw)
    except ObligationEvidenceIssuanceError as exc:
        raise ObligationEvidenceStoreError(str(exc)) from exc
    if issuance.issuance_sha256 != str(digest).strip().lower():
        raise ObligationEvidenceStoreError(
            "obligation issuance is stored under the wrong content identity"
        )
    if issuance.leaf_sha256 != expected_leaf:
        raise ObligationEvidenceStoreError(
            "obligation issuance is stored under the wrong leaf identity"
        )
    if _encoded(issuance.projection()) != path.read_bytes():
        raise ObligationEvidenceStoreError(
            "obligation issuance is not canonical JSON"
        )
    return issuance


def store_obligation_graph(
    root: Path,
    paper: str,
    graph: ObligationEvidenceGraph,
) -> Path:
    """Persist all leaves first, then atomically publish the complete graph."""

    # Rebuild the graph so a forged dataclass cannot bypass graph validation.
    parsed = build_obligation_graph(
        graph.leaves.values(), root_leaf_sha256s=graph.root_leaf_sha256s
    )
    if parsed.graph_sha256 != graph.graph_sha256:
        raise ObligationEvidenceStoreError("obligation graph dataclass is corrupt")
    for digest in parsed.topological_leaf_sha256s:
        store_obligation_leaf(root, paper, parsed.leaves[digest])
    path = graph_index_path(root, paper)
    _atomic_write(path, _encoded(parsed.projection()))
    # Publication is complete only after a fresh read authenticates every leaf.
    loaded = load_obligation_graph(root, paper)
    if loaded.graph_sha256 != parsed.graph_sha256:
        raise ObligationEvidenceStoreError("published obligation graph did not round-trip")
    return path


def load_obligation_graph(root: Path, paper: str) -> ObligationEvidenceGraph:
    """Load only the exact leaf set named by the current small graph index."""

    path = graph_index_path(root, paper)
    try:
        value = json.loads(path.read_bytes())
    except (OSError, UnicodeDecodeError, json.JSONDecodeError) as exc:
        raise ObligationEvidenceStoreError(f"obligation graph is unavailable: {exc}") from exc
    raw_digests = value.get("leaf_sha256s") if isinstance(value, Mapping) else None
    if not isinstance(raw_digests, list):
        raise ObligationEvidenceStoreError("obligation graph leaf index is malformed")
    leaves = {
        str(digest): load_obligation_leaf(root, paper, str(digest)).projection()
        for digest in raw_digests
    }
    try:
        graph = validate_obligation_graph(value, leaves=leaves)
    except ObligationEvidenceError as exc:
        raise ObligationEvidenceStoreError(str(exc)) from exc
    if _encoded(graph.projection()) != path.read_bytes():
        raise ObligationEvidenceStoreError("obligation graph is not canonical JSON")
    return graph


def store_obligation_leaves(
    root: Path,
    paper: str,
    leaves: Iterable[ObligationEvidenceLeaf],
) -> tuple[Path, ...]:
    """Persist successful leaves independently without publishing a graph."""

    return tuple(store_obligation_leaf(root, paper, leaf) for leaf in leaves)


def load_obligation_evidence_store_snapshot(
    root: Path,
    paper: str,
    required_graph: ObligationEvidenceGraph,
) -> ObligationEvidenceStoreSnapshot:
    """Load only objects addressable from one required graph.

    Missing objects are omitted. Existing malformed objects are represented by
    their expected content identity so the pure planner reports corruption
    instead of silently treating damaged evidence as absent. No repository-wide
    issuance scan or aggregate carrier parse is performed.
    """

    try:
        graph = validate_obligation_graph(
            required_graph.projection(),
            leaves={
                digest: leaf.projection()
                for digest, leaf in required_graph.leaves.items()
            },
        )
    except ObligationEvidenceError as exc:
        raise ObligationEvidenceStoreError(str(exc)) from exc

    available: dict[str, object] = {}
    issuance_records: dict[str, Mapping[str, Any]] = {}
    for digest in graph.topological_leaf_sha256s:
        leaf_path = _leaf_path(root, paper, digest)
        try:
            available[digest] = json.loads(leaf_path.read_bytes())
        except FileNotFoundError:
            pass
        except (OSError, UnicodeDecodeError, json.JSONDecodeError):
            available[digest] = {}

        issuance_folder = _issuance_by_leaf_path(
            root,
            paper,
            digest,
            "0" * 64,
        ).parent
        try:
            candidates = sorted(
                path for path in issuance_folder.iterdir() if path.is_file()
            )
        except FileNotFoundError:
            candidates = []
        except OSError as exc:
            raise ObligationEvidenceStoreError(
                f"could not read leaf issuance index: {exc}"
            ) from exc
        for path in candidates:
            issuance_sha256 = path.stem.lower()
            if path.suffix != ".json" or not SHA256_RE.fullmatch(issuance_sha256):
                raise ObligationEvidenceStoreError(
                    "leaf issuance index contains an unexpected file"
                )
            try:
                raw = json.loads(path.read_bytes())
                parsed = validate_obligation_evidence_issuance(raw)
                if (
                    parsed.issuance_sha256 != issuance_sha256
                    or parsed.leaf_sha256 != digest
                    or _encoded(parsed.projection()) != path.read_bytes()
                ):
                    raise ObligationEvidenceIssuanceError(
                        "leaf issuance is stored under the wrong identity"
                    )
                record: Mapping[str, Any] = parsed.projection()
            except (
                OSError,
                UnicodeDecodeError,
                json.JSONDecodeError,
                ObligationEvidenceIssuanceError,
            ):
                # Preserve the attributable identity so the pure planner can
                # report `corrupt_issuance_sha256s` exactly.
                record = {"issuance_sha256": issuance_sha256}
            previous = issuance_records.get(issuance_sha256)
            if previous is not None and dict(previous) != dict(record):
                raise ObligationEvidenceStoreError(
                    "one issuance identity has conflicting leaf-index records"
                )
            issuance_records[issuance_sha256] = record
    return ObligationEvidenceStoreSnapshot(
        available_leaves=MappingProxyType(available),
        issuances=tuple(
            issuance_records[digest] for digest in sorted(issuance_records)
        ),
    )


def _load_json_object(path: Path, label: str) -> Mapping[str, Any]:
    try:
        value = json.loads(path.read_bytes())
    except (OSError, UnicodeDecodeError, json.JSONDecodeError) as exc:
        raise ObligationEvidenceStoreError(f"{label} is unavailable: {exc}") from exc
    if not isinstance(value, Mapping):
        raise ObligationEvidenceStoreError(f"{label} is not an object")
    return value


def _load_graph_object(
    root: Path,
    paper: str,
    digest: str,
) -> ObligationEvidenceGraph:
    path = _graph_object_path(root, paper, digest)
    value = _load_json_object(path, "obligation graph object")
    raw_digests = value.get("leaf_sha256s")
    if not isinstance(raw_digests, list):
        raise ObligationEvidenceStoreError(
            "obligation graph object leaf index is malformed"
        )
    leaves = {
        str(leaf_digest): load_obligation_leaf(root, paper, str(leaf_digest)).projection()
        for leaf_digest in raw_digests
    }
    try:
        graph = validate_obligation_graph(value, leaves=leaves)
    except ObligationEvidenceError as exc:
        raise ObligationEvidenceStoreError(str(exc)) from exc
    if graph.graph_sha256 != str(digest).strip().lower():
        raise ObligationEvidenceStoreError(
            "obligation graph object is stored under the wrong identity"
        )
    if _encoded(graph.projection()) != path.read_bytes():
        raise ObligationEvidenceStoreError(
            "obligation graph object is not canonical JSON"
        )
    return graph


def _packed_accepted_graph_payload(
    paper: str,
    credential: AcceptedObligationGraphCredential,
) -> dict[str, Any]:
    """Return the canonical portable transport for one accepted credential."""

    return {
        "schema": PACKED_ACCEPTED_GRAPH_SCHEMA,
        "paper": paper,
        "accepted_graph": credential.accepted_graph.projection(),
        "leaves": {
            digest: credential.accepted_graph.leaves[digest].projection()
            for digest in credential.accepted_graph.topological_leaf_sha256s
        },
        "paper_index": credential.paper_index.projection(),
    }


def _load_packed_accepted_graph_material(
    root: Path,
    paper: str,
    graph_sha256: str,
) -> tuple[ObligationEvidenceGraph, Mapping[str, Any]]:
    """Authenticate one packed graph transport without granting acceptance."""

    digest = str(graph_sha256 or "").strip().lower()
    if not SHA256_RE.fullmatch(digest):
        raise ObligationEvidenceStoreError(
            "packed accepted graph identity is not SHA-256"
        )
    path = _accepted_graph_pack_path(root, paper, digest)
    value = _load_json_object(path, "packed accepted obligation graph")
    required = {"schema", "paper", "accepted_graph", "leaves", "paper_index"}
    if (
        set(value) != required
        or value.get("schema") != PACKED_ACCEPTED_GRAPH_SCHEMA
        or value.get("paper") != paper
    ):
        raise ObligationEvidenceStoreError(
            "packed accepted obligation graph fields are malformed"
        )
    raw_graph = value.get("accepted_graph")
    raw_leaves = value.get("leaves")
    raw_index = value.get("paper_index")
    if not all(
        isinstance(item, Mapping)
        for item in (raw_graph, raw_leaves, raw_index)
    ):
        raise ObligationEvidenceStoreError(
            "packed accepted obligation graph objects are malformed"
        )
    assert isinstance(raw_graph, Mapping)
    assert isinstance(raw_leaves, Mapping)
    assert isinstance(raw_index, Mapping)
    if any(
        not isinstance(key, str)
        or not SHA256_RE.fullmatch(key)
        or not isinstance(leaf, Mapping)
        for key, leaf in raw_leaves.items()
    ):
        raise ObligationEvidenceStoreError(
            "packed accepted obligation graph leaf map is malformed"
        )
    try:
        graph = validate_obligation_graph(raw_graph, leaves=raw_leaves)
    except ObligationEvidenceError as exc:
        raise ObligationEvidenceStoreError(str(exc)) from exc
    if graph.graph_sha256 != digest:
        raise ObligationEvidenceStoreError(
            "packed accepted obligation graph is stored under the wrong identity"
        )
    canonical = {
        "schema": PACKED_ACCEPTED_GRAPH_SCHEMA,
        "paper": paper,
        "accepted_graph": graph.projection(),
        "leaves": {
            leaf_digest: graph.leaves[leaf_digest].projection()
            for leaf_digest in graph.topological_leaf_sha256s
        },
        "paper_index": dict(raw_index),
    }
    if _encoded(canonical) != path.read_bytes():
        raise ObligationEvidenceStoreError(
            "packed accepted obligation graph is not canonical JSON"
        )
    return graph, raw_index


def _current_accepted_graph_selection(
    root: Path,
    paper: str,
) -> tuple[int, str]:
    """Load the canonical current selector for either storage representation."""

    pointer_path = current_accepted_graph_path(root, paper)
    pointer = _load_json_object(
        pointer_path, "current accepted obligation graph pointer"
    )
    if (
        set(pointer) != {"schema", "graph_sha256"}
        or pointer.get("schema")
        not in {1, PACKED_ACCEPTED_GRAPH_POINTER_SCHEMA}
    ):
        raise ObligationEvidenceStoreError(
            "current accepted obligation graph pointer is malformed"
        )
    if _encoded(pointer) != pointer_path.read_bytes():
        raise ObligationEvidenceStoreError(
            "current accepted obligation graph pointer is not canonical JSON"
        )
    graph_sha256 = str(pointer.get("graph_sha256") or "").strip().lower()
    if not SHA256_RE.fullmatch(graph_sha256):
        raise ObligationEvidenceStoreError(
            "accepted obligation graph identity is not SHA-256"
        )
    return int(pointer["schema"]), graph_sha256


def load_recorded_current_accepted_obligation_graph(
    root: Path,
    paper: str,
    graph_sha256: str,
) -> ObligationEvidenceGraph:
    """Authenticate one recorded current-pointer graph without accepting it.

    This narrow projection checks the canonical pointer, the requested
    content identity, the graph object, and every content-addressed leaf.  It
    deliberately does not validate current paper structure, source bytes,
    Lean artifacts, issuers, or terminal controls, so callers may use it only
    for diagnostics or negative-only scheduling decisions.  Current closure
    still requires :func:`load_accepted_obligation_graph` through the canonical
    receipt validator.
    """

    expected = str(graph_sha256 or "").strip().lower()
    if not SHA256_RE.fullmatch(expected):
        raise ObligationEvidenceStoreError(
            "recorded accepted obligation graph identity is not SHA-256"
        )
    pointer_schema, selected = _current_accepted_graph_selection(
        root, paper
    )
    if selected != expected:
        raise ObligationEvidenceStoreError(
            "recorded closure receipt does not select the current accepted graph"
        )
    if pointer_schema == PACKED_ACCEPTED_GRAPH_POINTER_SCHEMA:
        graph, _raw_index = _load_packed_accepted_graph_material(
            root, paper, expected
        )
        return graph
    return _load_graph_object(root, paper, expected)


def load_accepted_obligation_graph(
    root: Path,
    paper: str,
    *,
    preflight: ObligationStructuralPreflight,
    authenticated_authority_sha256s: Iterable[str],
    graph_sha256: str | None = None,
    require_current_aggregate_identity: bool = True,
) -> AcceptedObligationGraphCredential:
    """Authenticate the selected accepted graph and its complete paper index.

    Callers that disable aggregate identity must separately perform terminal
    current-material revalidation.  Exact graph/index integrity and current
    route/source/prerequisite structure remain mandatory in either mode.
    """

    pointer_schema: int | None = None
    if graph_sha256 is None:
        pointer_schema, graph_sha256 = _current_accepted_graph_selection(
            root, paper
        )
    graph_sha256 = str(graph_sha256).strip().lower()
    if not SHA256_RE.fullmatch(graph_sha256):
        raise ObligationEvidenceStoreError(
            "accepted obligation graph identity is not SHA-256"
        )
    pack_path = _accepted_graph_pack_path(root, paper, graph_sha256)
    packed = (
        pointer_schema == PACKED_ACCEPTED_GRAPH_POINTER_SCHEMA
        or (pointer_schema is None and pack_path.is_file())
    )
    if packed:
        accepted, index_value = _load_packed_accepted_graph_material(
            root, paper, graph_sha256
        )
        index_path: Path | None = None
    else:
        accepted = _load_graph_object(root, paper, graph_sha256)
        index_value = None
        index_path = None
    if len(accepted.root_leaf_sha256s) != 1:
        raise ObligationEvidenceStoreError(
            "accepted obligation graph does not have one terminal root"
        )
    closure = accepted.leaves[accepted.root_leaf_sha256s[0]]
    raw_index_sha256 = str(
        closure.semantic_payload.get("paper_index_sha256") or ""
    ).strip().lower()
    if not SHA256_RE.fullmatch(raw_index_sha256):
        raise ObligationEvidenceStoreError(
            "accepted obligation graph root has a malformed paper-index identity"
        )
    if index_value is None:
        index_path = _paper_index_path(root, paper, raw_index_sha256)
        index_value = _load_json_object(index_path, "paper obligation index")
    try:
        paper_index = validate_paper_obligation_index(
            index_value,
            graph=build_obligation_graph(
                (
                    leaf
                    for digest, leaf in accepted.leaves.items()
                    if digest != closure.leaf_sha256
                ),
                root_leaf_sha256s=closure.depends_on,
            ),
            require_complete=True,
            preflight=preflight,
            require_current_aggregate_identity=(
                require_current_aggregate_identity
            ),
        )
        credential = validate_accepted_obligation_graph(
            accepted,
            paper_index,
            preflight=preflight,
            authenticated_authority_sha256s=authenticated_authority_sha256s,
            require_current_aggregate_identity=(
                require_current_aggregate_identity
            ),
        )
    except (
        AcceptedObligationGraphError,
        ObligationEvidenceError,
        PaperObligationIndexError,
    ) as exc:
        raise ObligationEvidenceStoreError(str(exc)) from exc
    if paper_index.index_sha256 != raw_index_sha256:
        raise ObligationEvidenceStoreError(
            "paper obligation index is stored under the wrong identity"
        )
    if index_path is not None and (
        _encoded(paper_index.projection()) != index_path.read_bytes()
    ):
        raise ObligationEvidenceStoreError(
            "paper obligation index is not canonical JSON"
        )
    if index_path is None and paper_index.projection() != index_value:
        raise ObligationEvidenceStoreError(
            "packed paper obligation index is not canonical"
        )
    return credential


def store_accepted_obligation_graph(
    root: Path,
    paper: str,
    paper_index: PaperObligationIndex,
    semantic_graph: ObligationEvidenceGraph,
    *,
    preflight: ObligationStructuralPreflight,
    strict_closeout_authority: StrictCloseoutAuthority,
    final_holistic_audit_surface_sha256: str,
    source_assurance_sha256: str,
) -> Path:
    """Atomically select one immutable packed accepted-graph object."""

    try:
        credential = build_accepted_obligation_graph(
            semantic_graph,
            paper_index,
            preflight=preflight,
            strict_closeout_authority=strict_closeout_authority,
            final_holistic_audit_surface_sha256=(
                final_holistic_audit_surface_sha256
            ),
            source_assurance_sha256=source_assurance_sha256,
        )
    except AcceptedObligationGraphError as exc:
        raise ObligationEvidenceStoreError(str(exc)) from exc
    pack_path = _accepted_graph_pack_path(
        root, paper, credential.graph_sha256
    )
    _store_immutable_object(
        pack_path,
        _packed_accepted_graph_payload(paper, credential),
        "packed accepted obligation graph",
    )
    loaded = load_accepted_obligation_graph(
        root,
        paper,
        preflight=preflight,
        authenticated_authority_sha256s=[
            strict_closeout_authority.engine_tree_sha256
        ],
        graph_sha256=credential.graph_sha256,
    )
    if loaded != credential:
        raise ObligationEvidenceStoreError(
            "published accepted obligation graph did not round-trip"
        )
    pointer_path = current_accepted_graph_path(root, paper)
    _atomic_write(
        pointer_path,
        _encoded(
            {
                "schema": PACKED_ACCEPTED_GRAPH_POINTER_SCHEMA,
                "graph_sha256": credential.graph_sha256,
            }
        ),
    )
    selected = load_accepted_obligation_graph(
        root,
        paper,
        preflight=preflight,
        authenticated_authority_sha256s=[
            strict_closeout_authority.engine_tree_sha256
        ],
    )
    if selected != credential:
        raise ObligationEvidenceStoreError(
            "current accepted obligation graph did not round-trip"
        )
    return pointer_path


def load_paper_obligation_bundle(
    root: Path,
    paper: str,
    *,
    bundle_sha256: str | None = None,
) -> LoadedPaperObligationBundle:
    """Authenticate one complete bundle or the atomically selected current one."""

    if bundle_sha256 is None:
        pointer_path = current_bundle_path(root, paper)
        pointer = _load_json_object(pointer_path, "current obligation bundle pointer")
        if set(pointer) != {"schema", "bundle_sha256"} or pointer.get("schema") != 1:
            raise ObligationEvidenceStoreError(
                "current obligation bundle pointer is malformed"
            )
        bundle_sha256 = str(pointer.get("bundle_sha256") or "").strip().lower()
        if not SHA256_RE.fullmatch(bundle_sha256):
            raise ObligationEvidenceStoreError(
                "current obligation bundle pointer identity is malformed"
            )
        if _encoded(pointer) != pointer_path.read_bytes():
            raise ObligationEvidenceStoreError(
                "current obligation bundle pointer is not canonical JSON"
            )
    else:
        bundle_sha256 = str(bundle_sha256).strip().lower()
        if not SHA256_RE.fullmatch(bundle_sha256):
            raise ObligationEvidenceStoreError("bundle identity is not SHA-256")

    bundle_path = _bundle_path(root, paper, bundle_sha256)
    bundle_value = _load_json_object(bundle_path, "paper obligation bundle")
    raw_graph_sha256 = str(bundle_value.get("graph_sha256") or "").strip().lower()
    raw_index_sha256 = str(bundle_value.get("paper_index_sha256") or "").strip().lower()
    if not SHA256_RE.fullmatch(raw_graph_sha256) or not SHA256_RE.fullmatch(
        raw_index_sha256
    ):
        raise ObligationEvidenceStoreError(
            "paper obligation bundle object references malformed identities"
        )
    graph = _load_graph_object(root, paper, raw_graph_sha256)
    index_path = _paper_index_path(root, paper, raw_index_sha256)
    index_value = _load_json_object(index_path, "paper obligation index")
    try:
        paper_index = validate_paper_obligation_index(
            index_value,
            graph=graph,
            require_complete=False,
        )
    except PaperObligationIndexError as exc:
        raise ObligationEvidenceStoreError(str(exc)) from exc
    if paper_index.index_sha256 != raw_index_sha256:
        raise ObligationEvidenceStoreError(
            "paper obligation index is stored under the wrong identity"
        )
    if _encoded(paper_index.projection()) != index_path.read_bytes():
        raise ObligationEvidenceStoreError(
            "paper obligation index is not canonical JSON"
        )

    raw_issuances = bundle_value.get("issuance_sha256s_by_leaf")
    if not isinstance(raw_issuances, Mapping):
        raise ObligationEvidenceStoreError(
            "paper obligation bundle issuance index is malformed"
        )
    issuances: dict[str, ObligationEvidenceIssuance] = {}
    for raw_leaf, raw_ids in raw_issuances.items():
        leaf_sha256 = str(raw_leaf).strip().lower()
        if not SHA256_RE.fullmatch(leaf_sha256):
            raise ObligationEvidenceStoreError(
                "paper obligation bundle leaf identity is malformed"
            )
        if not isinstance(raw_ids, list):
            raise ObligationEvidenceStoreError(
                "paper obligation bundle issuance list is malformed"
            )
        for raw_digest in raw_ids:
            digest = str(raw_digest).strip().lower()
            issuance = load_obligation_evidence_issuance(
                root, paper, leaf_sha256, digest
            )
            prior = issuances.get(digest)
            if prior is not None and prior != issuance:
                raise ObligationEvidenceStoreError(
                    "paper obligation bundle reuses an issuance identity with conflicting content"
                )
            issuances[digest] = issuance
    try:
        bundle = validate_paper_obligation_bundle(
            bundle_value,
            paper_index=paper_index,
            graph=graph,
            issuances=issuances,
        )
    except PaperObligationBundleError as exc:
        raise ObligationEvidenceStoreError(str(exc)) from exc
    if bundle.bundle_sha256 != bundle_sha256:
        raise ObligationEvidenceStoreError(
            "paper obligation bundle is stored under the wrong identity"
        )
    if _encoded(bundle.projection()) != bundle_path.read_bytes():
        raise ObligationEvidenceStoreError(
            "paper obligation bundle is not canonical JSON"
        )
    return LoadedPaperObligationBundle(
        bundle=bundle,
        paper_index=paper_index,
        graph=graph,
        issuances=MappingProxyType(issuances),
    )


def store_paper_obligation_bundle(
    root: Path,
    paper: str,
    paper_index: PaperObligationIndex,
    graph: ObligationEvidenceGraph,
    issuances: Iterable[ObligationEvidenceIssuance | Mapping[str, Any]],
    *,
    preflight: ObligationStructuralPreflight,
) -> Path:
    """Durably publish a complete bundle without risking the prior selection.

    Leaves, issuances, graph, paper index, and bundle are immutable objects.
    The tiny current pointer changes only after a fresh read authenticates every
    new object, so interruption cannot replace a previously valid selection.
    """

    return _store_paper_obligation_bundle(
        root,
        paper,
        paper_index,
        graph,
        issuances,
        preflight=preflight,
        accepting=False,
    )


def store_accepting_paper_obligation_bundle(
    root: Path,
    paper: str,
    paper_index: PaperObligationIndex,
    graph: ObligationEvidenceGraph,
    issuances: Iterable[ObligationEvidenceIssuance | Mapping[str, Any]],
    *,
    preflight: ObligationStructuralPreflight,
) -> Path:
    """Publish the sole accepting bundle after terminal verification."""

    return _store_paper_obligation_bundle(
        root,
        paper,
        paper_index,
        graph,
        issuances,
        preflight=preflight,
        accepting=True,
    )


def _store_paper_obligation_bundle(
    root: Path,
    paper: str,
    paper_index: PaperObligationIndex,
    graph: ObligationEvidenceGraph,
    issuances: Iterable[ObligationEvidenceIssuance | Mapping[str, Any]],
    *,
    preflight: ObligationStructuralPreflight,
    accepting: bool,
) -> Path:
    issuance_values = tuple(issuances)
    try:
        index = validate_paper_obligation_index(
            paper_index.projection(),
            graph=graph,
            require_complete=True,
            preflight=preflight,
        )
        bundle = (
            build_accepting_paper_obligation_bundle(
                index,
                graph,
                issuance_values,
                preflight=preflight,
            )
            if accepting
            else build_paper_obligation_bundle(
                index,
                graph,
                issuance_values,
                preflight=preflight,
            )
        )
    except (PaperObligationIndexError, PaperObligationBundleError) as exc:
        raise ObligationEvidenceStoreError(str(exc)) from exc

    for digest in graph.topological_leaf_sha256s:
        store_obligation_leaf(root, paper, graph.leaves[digest])
    for issuance in issuance_values:
        store_obligation_evidence_issuance(root, paper, issuance)

    graph_path = _graph_object_path(root, paper, graph.graph_sha256)
    _store_immutable_object(graph_path, graph.projection(), "obligation graph object")
    index_path = _paper_index_path(root, paper, index.index_sha256)
    _store_immutable_object(index_path, index.projection(), "paper obligation index")
    bundle_path = _bundle_path(root, paper, bundle.bundle_sha256)
    _store_immutable_object(bundle_path, bundle.projection(), "paper obligation bundle")

    # Authenticate the new object graph before changing the current pointer.
    loaded = load_paper_obligation_bundle(
        root,
        paper,
        bundle_sha256=bundle.bundle_sha256,
    )
    if loaded.bundle != bundle:
        raise ObligationEvidenceStoreError(
            "published paper obligation bundle did not round-trip"
        )
    pointer_path = current_bundle_path(root, paper)
    _atomic_write(
        pointer_path,
        _encoded({"schema": 1, "bundle_sha256": bundle.bundle_sha256}),
    )
    # The selected current state is complete only after the pointer round-trips.
    if load_paper_obligation_bundle(root, paper).bundle != bundle:
        raise ObligationEvidenceStoreError(
            "current paper obligation bundle did not round-trip"
        )
    return pointer_path
