#!/usr/bin/env python3
"""Small cache boundary for source-record Lean manifest reuse.

This module owns only cache routing.  It does not generate or validate a raw
source-record audit.  Every reusable manifest remains authenticated by the
tracked authority, ignored carrier, exact compiled context, current parsed
Lean declaration, and the shared manifest-store validator.
"""

from __future__ import annotations

import re
from pathlib import Path
from typing import Any, Callable, Iterable, Mapping

from scripts.authenticated_manifest_store import (
    configured_review_row_proposition_graph_sha256,
    elaborated_proposition_graph_sha256,
    merge_authenticated_manifest_store,
    prime_exact_context_attested_resume_manifests,
)
from scripts.lean_signature_manifest import (
    semantic_dependency_manifest,
    signature_manifest_digest,
)


SHA256_RE = re.compile(r"^[0-9a-f]{64}$")
LEAN_NAME_COMPONENT_PATTERN = r"(?:«[^»\n]+»|[^\s.:(){}\[\],]+)"
LEAN_QUALIFIED_NAME_PATTERN = (
    rf"{LEAN_NAME_COMPONENT_PATTERN}(?:\.{LEAN_NAME_COMPONENT_PATTERN})*"
)


def qualified_identity(value: object) -> str:
    identity = str(value or "").strip()
    if "." not in identity or not re.fullmatch(LEAN_QUALIFIED_NAME_PATTERN, identity):
        return ""
    return identity


def current_manifest_resume_bindings(
    *,
    paper_dir: Path,
    qualified_row_refs: Mapping[str, str],
    selected_row_source_paths: Mapping[str, Path],
    source_text_by_path: Mapping[Path, str],
    parse_review_source_declarations: Callable[..., Iterable[tuple[Any, ...]]],
) -> tuple[dict[str, dict[str, Any]], set[str]]:
    """Build exact declaration bindings from one frozen source snapshot."""

    requested: dict[str, Path] = {}
    duplicates: set[str] = set()
    for row, raw_qualified in qualified_row_refs.items():
        qualified = qualified_identity(raw_qualified)
        source_path = selected_row_source_paths.get(row)
        if not qualified or not isinstance(source_path, Path):
            continue
        if qualified in requested and requested[qualified].resolve() != source_path.resolve():
            duplicates.add(qualified)
            requested.pop(qualified, None)
        elif qualified not in duplicates:
            requested[qualified] = source_path

    parsed_by_qualified: dict[str, tuple[str, str, int, Path]] = {}
    for source_path in sorted(set(requested.values())):
        try:
            text = source_text_by_path[source_path.resolve()]
        except (KeyError, OSError):
            for qualified, expected_path in requested.items():
                if expected_path.resolve() == source_path.resolve():
                    duplicates.add(qualified)
            continue
        for (
            kind,
            _name,
            full_name,
            raw_signature,
            _comment,
            line_number,
            parsed_path,
        ) in parse_review_source_declarations(source_path, source_text=text):
            if full_name not in requested or requested[full_name].resolve() != parsed_path.resolve():
                continue
            if full_name in parsed_by_qualified:
                duplicates.add(full_name)
                parsed_by_qualified.pop(full_name, None)
                continue
            parsed_by_qualified[full_name] = (
                str(kind),
                str(raw_signature),
                int(line_number),
                parsed_path,
            )

    bindings: dict[str, dict[str, Any]] = {}
    folder_root = paper_dir.resolve()
    for qualified in requested:
        if qualified in duplicates:
            continue
        parsed = parsed_by_qualified.get(qualified)
        if parsed is None:
            continue
        kind, raw_signature, line_number, parsed_path = parsed
        try:
            source_file = parsed_path.resolve().relative_to(folder_root).as_posix()
        except (OSError, ValueError):
            duplicates.add(qualified)
            continue
        bindings[qualified] = {
            "qualified_declaration": qualified,
            "source_file": source_file,
            "declaration_kind": kind,
            "lean_source_declaration": raw_signature,
            "line_number": line_number,
        }
    return bindings, duplicates


def local_declaration_manifest_bindings(
    *,
    root: Path,
    paper_dir: Path,
    declarations: Iterable[object],
    requested_declarations: Iterable[str] = (),
) -> tuple[dict[str, dict[str, Any]], set[str]]:
    """Bind every unique paper-local declaration parsed by the raw producer."""

    requested = {
        qualified_identity(value)
        for value in requested_declarations
        if qualified_identity(value)
    }
    bindings: dict[str, dict[str, Any]] = {}
    duplicates: set[str] = set()
    root_resolved = root.resolve()
    paper_resolved = paper_dir.resolve()
    for declaration in declarations:
        qualified = qualified_identity(getattr(declaration, "name", ""))
        if not qualified or (requested and qualified not in requested):
            continue
        try:
            source_path = (root_resolved / str(declaration.source_file)).resolve()
            source_file = source_path.relative_to(paper_resolved).as_posix()
            line_number = int(declaration.line)
        except (AttributeError, OSError, TypeError, ValueError):
            duplicates.add(qualified)
            bindings.pop(qualified, None)
            continue
        binding = {
            "qualified_declaration": qualified,
            "source_file": source_file,
            "declaration_kind": str(declaration.kind),
            "lean_source_declaration": str(declaration.source),
            "line_number": line_number,
        }
        if qualified in bindings:
            duplicates.add(qualified)
            bindings.pop(qualified, None)
        elif qualified not in duplicates:
            bindings[qualified] = binding
    return bindings, duplicates


def prime_signature_manifest_store(
    *,
    root: Path,
    paper_dir: Path,
    import_module: str | None,
    semantic_dependency_modules: tuple[str, ...],
    current_context: Mapping[str, Any] | None,
    current_bindings: Mapping[str, Mapping[str, Any]] | None,
    resume_records_provider: Callable[..., Mapping[str, Any]],
    attester: Callable[..., tuple[dict[str, dict[str, Any]], dict[str, Any]]] = (
        prime_exact_context_attested_resume_manifests
    ),
) -> tuple[dict[str, dict[str, Any]], dict[str, Any]]:
    """Prime only journal rows tied to independent current source bindings."""

    deferred = {
        "schema": 1,
        "paper": paper_dir.name,
        "candidate_count": 0,
        "context_count": 0,
        "accepted_context_count": 0,
        "context_provider_call_count": 0,
        "seeded_count": 0,
        "seeded_declarations": [],
        "fresh_required_count": 0,
        "rejected_by_reason": {},
        "store_status": "deferred_without_current_source_bindings",
    }
    if (
        not import_module
        or not semantic_dependency_modules
        or not isinstance(current_context, Mapping)
        or not current_bindings
    ):
        return {}, deferred
    try:
        resume_records = resume_records_provider(
            paper_dir,
            context=current_context,
            bindings=current_bindings,
        )
    except Exception:  # noqa: BLE001 - ignored journal data is only a hint.
        return {}, {
            **deferred,
            "store_status": "resume_records_unavailable",
            "fresh_required_count": len(current_bindings),
        }
    try:
        return attester(
            root=root,
            paper_dir=paper_dir,
            import_module=import_module,
            semantic_dependency_modules=semantic_dependency_modules,
            current_context=current_context,
            current_bindings=current_bindings,
            resume_records=resume_records,
        )
    except Exception:  # noqa: BLE001 - failed optimization remains a miss.
        return {}, {
            **deferred,
            "store_status": "resume_attestation_unavailable",
            "fresh_required_count": len(current_bindings),
        }


def publish_signature_manifest_store(
    *,
    root: Path,
    paper_dir: Path,
    import_module: str,
    semantic_dependency_modules: tuple[str, ...],
    configured_review_rows: Iterable[Mapping[str, Any]],
    manifests: Mapping[str, Mapping[str, Any]],
    context: Mapping[str, Any],
    configured_source_bindings: Mapping[str, Mapping[str, Any]] | None = None,
    merger: Callable[..., set[str]] = merge_authenticated_manifest_store,
    signature_digest: Callable[[Mapping[str, Any]], str] = signature_manifest_digest,
    dependency_manifest: Callable[[Mapping[str, Any]], Mapping[str, Any]] = (
        semantic_dependency_manifest
    ),
) -> set[str]:
    """Publish manifests from one successful raw scan into the shared store.

    When an exact frozen source binding is available for a configured row, the
    producer uses the same authority-binding schema reconstructed by the
    dashboard.  That single contract prevents valid manifests from becoming
    systematic cache misses merely because two producers serialized the same
    declaration coordinate differently.
    """

    if not isinstance(context, Mapping):
        return set()
    configured_source_bindings = configured_source_bindings or {}
    configured_rows_by_qualified: dict[str, Mapping[str, Any]] = {}
    duplicate_configured: set[str] = set()
    for raw_row in configured_review_rows:
        if not isinstance(raw_row, Mapping):
            continue
        qualified = qualified_identity(raw_row.get("qualified_declaration"))
        if not qualified:
            continue
        if qualified in configured_rows_by_qualified:
            duplicate_configured.add(qualified)
            configured_rows_by_qualified.pop(qualified, None)
        elif qualified not in duplicate_configured:
            configured_rows_by_qualified[qualified] = raw_row

    candidates: list[dict[str, Any]] = []
    for raw_qualified, manifest in sorted(manifests.items(), key=lambda item: str(item[0])):
        qualified = qualified_identity(raw_qualified)
        if (
            not qualified
            or qualified != str(raw_qualified).strip()
            or qualified in duplicate_configured
            or not isinstance(manifest, Mapping)
        ):
            continue
        signature = signature_digest(manifest)
        dependency = dependency_manifest(manifest)
        dependency_sha256 = (
            str(dependency.get("semantic_dependency_sha256") or "").strip().lower()
            if isinstance(dependency, Mapping)
            else ""
        )
        proposition_graph_sha256 = elaborated_proposition_graph_sha256(
            manifest.get("elaborated_proposition_graph")
        )
        if not all(
            SHA256_RE.fullmatch(value)
            for value in (signature, dependency_sha256, proposition_graph_sha256)
        ):
            continue
        raw_row = configured_rows_by_qualified.get(qualified)
        if raw_row is not None and (
            signature
            != str(raw_row.get("elaborated_signature_sha256") or "").strip().lower()
            or dependency_sha256
            != str(raw_row.get("semantic_dependency_sha256") or "").strip().lower()
            or proposition_graph_sha256
            != configured_review_row_proposition_graph_sha256(raw_row)
        ):
            continue
        source_binding = configured_source_bindings.get(qualified)
        if isinstance(source_binding, Mapping):
            try:
                from scripts.review_dashboard import (
                    review_signature_manifest_authority_binding,
                )

                authority_binding = review_signature_manifest_authority_binding(
                    qualified_declaration=qualified,
                    source_file=str(source_binding.get("source_file") or ""),
                    lean_source_declaration=str(
                        source_binding.get("lean_source_declaration") or ""
                    ),
                    line_number=int(source_binding.get("line_number")),
                    declaration_kind=str(
                        source_binding.get("declaration_kind") or ""
                    ),
                    elaborated_signature_sha256=signature,
                    elaborated_proposition_graph_sha256=proposition_graph_sha256,
                )
            except (ImportError, TypeError, ValueError):
                continue
        elif raw_row is not None:
            # Compatibility for old callers and fixtures.  Production raw
            # publication supplies the frozen source bindings above.
            authority_binding = {
                key: raw_row.get(key)
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
                    "elaborated_proposition_graph_sha256",
                )
            }
        else:
            authority_binding = {
                "schema": 1,
                "kind": "successful_source_record_manifest",
                "qualified_declaration": qualified,
                "elaborated_signature_sha256": signature,
                "semantic_dependency_sha256": dependency_sha256,
                "elaborated_proposition_graph_sha256": proposition_graph_sha256,
            }
        candidates.append(
            {
                "qualified_declaration": qualified,
                "manifest": manifest,
                "context": context,
                "authority_binding": authority_binding,
            }
        )
    stored_declarations = merger(
        paper_dir=paper_dir,
        paper=paper_dir.name,
        candidates=candidates,
    )
    candidate_declarations = {
        str(candidate["qualified_declaration"]).strip()
        for candidate in candidates
        if isinstance(candidate.get("qualified_declaration"), str)
        and str(candidate["qualified_declaration"]).strip()
    }
    return candidate_declarations & set(stored_declarations)


def checkpoint_manifest_resume_cache(
    *,
    paper_dir: Path,
    context: Mapping[str, Any],
    published_declarations: Iterable[str],
    resume_bindings: Mapping[str, Mapping[str, Any]],
    manifests: Mapping[str, Mapping[str, Any]],
    checkpoint: Callable[..., set[str]],
) -> set[str]:
    """Checkpoint only source-bound roots accepted by store publication."""

    accepted = {
        str(qualified).strip()
        for qualified in published_declarations
        if isinstance(qualified, str) and str(qualified).strip()
    }
    candidates = {
        qualified: dict(raw_manifest)
        for qualified, raw_manifest in manifests.items()
        if (
            isinstance(qualified, str)
            and qualified in accepted
            and qualified in resume_bindings
            and isinstance(raw_manifest, Mapping)
        )
    }
    if not candidates:
        return set()
    try:
        checkpointed = checkpoint(
            paper_dir,
            resume_bindings,
            context,
            candidates,
        )
    except Exception:  # noqa: BLE001 - cache persistence remains best effort.
        return set()
    if not isinstance(checkpointed, set):
        return set()
    return {qualified for qualified in checkpointed if qualified in candidates}
