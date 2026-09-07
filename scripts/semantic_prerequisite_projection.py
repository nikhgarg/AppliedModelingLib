"""Project exact Lean semantic prerequisites against raw-source review ledgers.

This module is the acceptance-neutral projection shared by closeout and review
presentation.  It owns no Lean discovery, dashboard registry, public-release
fallback, build, or filesystem enumeration.  Callers supply the complete
Lean-owned target surface, exact declaration-source records, source map, and
review ledger.  A closeout caller must additionally supply its frozen file-byte
snapshot, so source-anchor validation cannot fall through to live bytes.
"""

from __future__ import annotations

import hashlib
import re
from pathlib import Path
from typing import Any, Iterable, Mapping

from scripts.lean_review_surface import lean_source_range_text
from scripts.obligation_routes import EvidenceRouteSet, ObligationRouteError, RouteKind
from scripts.semantic_review_binding import (
    reusable_semantic_judgment,
    unique_reusable_judgment_bindings,
)
from scripts.source_review_input import (
    source_anchor_file_error,
    source_semantic_input_bundle,
)
from scripts.corrected_target_identity import (
    APPROVED_CORRECTED_TARGET_MATCH,
    corrected_target_screening_binding_is_current,
    corrected_target_review_digest,
    source_requires_approved_corrected_target,
)


V11_LEAN_TARGET_PROTOCOL = "lean_transparent_paper_expansion_with_claim_atoms_v2"
V11_DEFINITION_TARGET_PROTOCOL = "lean_paper_definition_declaration_display_v1"

PAPER_PREREQUISITE_SCHEMA = 1
PAPER_PREREQUISITE_PROMPT_VERSION = (
    "paper-prerequisite-match-v2-verbatim-source-anchor-lean-expanded-target-exact-code"
)
PAPER_PREREQUISITE_TARGET_PROTOCOL = "lean_paper_declaration_display_v1"

LIBRARY_SEMANTIC_REVIEW_SCHEMA = 1
REQUIRED_LLM_LIBRARY_SEMANTIC_REVIEW_PROMPT_VERSION = (
    "library-statement-match-v2-verbatim-source-anchor-lean-display-exact-code"
)
LIBRARY_SEMANTIC_TARGET_PROTOCOL = "lean-library-display-plus-exact-code-v1"

LOCAL_SOURCE_CONNECTION_STATE = "locally_byte_verified"
PUBLIC_SOURCE_DISPLAY_PROJECTION_STATE = "release_projected_excerpt"

_SHA256_RE = re.compile(r"[0-9a-f]{64}")
_JUDGMENTS = frozenset(
    {"matches", "matches_approved_corrected_target", "mismatch", "uncertain"}
)


def empty_paper_semantic_prerequisite_ledger(paper: str) -> dict[str, Any]:
    """Return the canonical ledger for a Lean-proved empty paper surface."""

    return {
        "schema": PAPER_PREREQUISITE_SCHEMA,
        "paper": paper,
        "prompt_version": PAPER_PREREQUISITE_PROMPT_VERSION,
        "target_protocol": PAPER_PREREQUISITE_TARGET_PROTOCOL,
        "comment": (
            "Lean's current expanded source-claim surface retains no paper-local "
            "semantic prerequisites outside the directly reviewed Specs."
        ),
        "items": {},
    }


def lean_graph_library_declaration_sources(
    repository_root: Path,
    *,
    semantic_targets: Mapping[str, Mapping[str, Any]],
    semantic_target_errors: Mapping[str, str],
    file_bytes_override: Mapping[Path, bytes | None] | None,
) -> dict[str, dict[str, Any]]:
    """Slice exact reusable declarations from Lean-owned graph coordinates.

    The current v11 graph has already classified each reusable semantic review
    root and collapsed generated declarations to a unique source-presented
    owner.  Python therefore does not need a declaration-name registry, a
    structure-projection table, a Lean parser, or historical line hints here.
    It validates the graph's exact owner/module/range coordinates against the
    frozen module bytes and exposes the selected bytes to the ordinary
    source-to-library projection.

    A malformed or unavailable coordinate becomes a declaration-local error;
    it never falls through to repository scanning or name-based discovery.
    """

    root = repository_root.resolve()
    names = {
        str(name).strip()
        for name in (*semantic_targets.keys(), *semantic_target_errors.keys())
        if str(name).strip()
    }
    sources: dict[str, dict[str, Any]] = {}
    for name in sorted(names):
        raw_target = semantic_targets.get(name)
        target = dict(raw_target) if isinstance(raw_target, Mapping) else {}
        owner = str(target.get("review_owner_declaration") or "").strip()
        module = str(target.get("source_module") or "").strip()
        raw_range = {
            "line_start": target.get("source_line_start"),
            "column_start": target.get("source_column_start"),
            "line_end": target.get("source_line_end"),
            "column_end": target.get("source_column_end"),
        }
        error = ""
        relative_path = ""
        content: bytes | None = None
        path: Path | None = None
        if not target:
            error = str(semantic_target_errors.get(name) or "").strip()
            error = error or "Lean graph produced no reusable semantic target"
        elif owner != name:
            error = "Lean graph reusable target has no exact source-presented owner"
        elif not module:
            error = "Lean graph reusable target has no source module"
        else:
            path = (root / (module.replace(".", "/") + ".lean")).resolve()
            try:
                relative_path = path.relative_to(root).as_posix()
            except ValueError:
                error = "Lean graph reusable target resolves outside the repository"
            if not error:
                if file_bytes_override is not None:
                    if path not in file_bytes_override:
                        error = (
                            "Lean-owned reusable declaration is absent from the "
                            "frozen graph snapshot"
                        )
                    else:
                        content = file_bytes_override[path]
                else:
                    try:
                        content = path.read_bytes()
                    except OSError as exc:
                        error = f"could not read Lean-owned reusable declaration: {exc}"
        definition = (
            lean_source_range_text(content, raw_range)
            if content is not None and not error
            else None
        )
        if not error and definition is None:
            error = "Lean-owned reusable declaration range is malformed or empty"
        definition_text = definition or ""
        definition_digest = (
            hashlib.sha256(definition_text.encode("utf-8")).hexdigest()
            if definition_text
            else ""
        )
        sources[name] = {
            "library_definition": definition_text,
            "library_definition_sha256": definition_digest,
            "current_named_library_definition_sha256": definition_digest,
            "library_definition_error": error,
            "library_source_path": relative_path,
            "library_line_start": raw_range["line_start"],
            "library_line_end": raw_range["line_end"],
        }
    return sources


def _clean_mapping(value: object) -> dict[str, Any]:
    return dict(value) if isinstance(value, Mapping) else {}


def source_map_items_by_key(payload: Mapping[str, Any]) -> dict[str, Mapping[str, Any]]:
    """Index exact statement-map items without accepting navigation prose."""

    raw_items = payload.get("items")
    if isinstance(raw_items, Mapping):
        return {
            str(key).strip(): value
            for key, value in raw_items.items()
            if str(key).strip() and isinstance(value, Mapping)
        }
    if isinstance(raw_items, list):
        out: dict[str, Mapping[str, Any]] = {}
        for raw in raw_items:
            if not isinstance(raw, Mapping):
                continue
            key = str(raw.get("id") or raw.get("source_item") or "").strip()
            if key:
                out[key] = raw
        return out
    return {}


def selected_paper_semantic_prerequisite_targets(
    source_map: Mapping[str, Any],
    prerequisite_semantic_targets: Mapping[str, Mapping[str, Any]],
) -> dict[str, Mapping[str, Any]]:
    """Select the source-mapped paper-local review boundary from a Lean graph.

    Lean owns the *complete* paper-local dependency closure. A source-to-Lean
    semantic review belongs only to declarations explicitly marked as
    source-semantic boundaries in the typed statement map. Internal Lean
    helpers remain in the elaborated proof closure and are checked as
    realization support; Python never promotes them into paper-source claims.

    The explicit ``paper_semantic_prerequisite_sources`` map must cover every
    current paper-local ``source_semantic_declaration`` root and nothing else.
    This is a structural validation of Lean-produced graph data and the typed
    source map. It does not parse Lean, infer source ownership, or judge text.
    """

    current_targets = {
        str(name).strip(): target
        for name, target in prerequisite_semantic_targets.items()
        if str(name).strip() and isinstance(target, Mapping)
    }
    # Historical closeouts predate the typed source-boundary contract.  Preserve
    # their recorded denominator for archival verification; they cannot obtain
    # a new current-protocol semantic-review transaction until migration adds
    # schema 2 and its explicit boundary map.
    if source_map.get("semantic_route_schema") != 2:
        return dict(current_targets)
    try:
        routes = EvidenceRouteSet.from_source_map(source_map)
    except ObligationRouteError as exc:
        raise ValueError("invalid typed source route surface: " + str(exc)) from exc

    raw_explicit = source_map.get("paper_semantic_prerequisite_sources", {})
    if raw_explicit is None:
        raw_explicit = {}
    if not isinstance(raw_explicit, Mapping) or not all(
        isinstance(declaration, str)
        and declaration.strip()
        and isinstance(source_item, str)
        and source_item.strip()
        for declaration, source_item in raw_explicit.items()
    ):
        raise ValueError(
            "paper_semantic_prerequisite_sources must map nonempty Lean "
            "declaration names to nonempty source-item ids"
        )
    explicit = {
        str(declaration).strip(): str(source_item).strip()
        for declaration, source_item in raw_explicit.items()
    }
    source_items = source_map_items_by_key(source_map)
    unknown_source_items = sorted(set(explicit.values()) - set(source_items))
    if unknown_source_items:
        raise ValueError(
            "paper_semantic_prerequisite_sources names absent source items: "
            + ", ".join(unknown_source_items)
        )
    unknown_declarations = sorted(set(explicit) - set(current_targets))
    if unknown_declarations:
        raise ValueError(
            "paper_semantic_prerequisite_sources names outside the current "
            "Lean prerequisite surface: "
            + ", ".join(unknown_declarations)
        )

    routed_roots = {
        declaration
        for route in routes.routes
        if route.route_kind is RouteKind.SOURCE_SEMANTIC_DECLARATION
        for declaration in route.semantic_declarations
        if declaration in current_targets
    }
    missing = sorted(routed_roots - set(explicit))
    if missing:
        raise ValueError(
            "current paper-local source-semantic declaration(s) lack an "
            "explicit paper_semantic_prerequisite_sources route: "
            + ", ".join(missing)
        )
    non_boundary = sorted(set(explicit) - routed_roots)
    if non_boundary:
        raise ValueError(
            "paper_semantic_prerequisite_sources selects declaration(s) that "
            "are not current paper-local source-semantic roots: "
            + ", ".join(non_boundary)
        )
    return {name: current_targets[name] for name in sorted(explicit)}


def selected_library_semantic_prerequisite_targets(
    source_map: Mapping[str, Any],
    prerequisite_semantic_targets: Mapping[str, Mapping[str, Any]],
) -> dict[str, Mapping[str, Any]]:
    """Select source-mapped reusable roots from Lean's complete closure.

    Lean retains every reachable reusable declaration in the dependency graph so
    proof, import, and axiom checks remain complete. A source-to-Lean library
    review, however, is required only for a material reusable declaration with
    an explicit byte-pinned paper-source connection. The typed map provides
    that boundary. Recursive proof helpers remain graph-checked support rather
    than synthetic paper-source rows without a source statement to compare.

    This is location-neutral. A routed source declaration that Lean owns in a
    reusable module must appear in the explicit map; an additional reusable
    root may also be selected when a paper-local alias is the routed source
    declaration and the reusable implementation itself needs direct screening.
    Python validates only the typed map against Lean-emitted target keys.
    """

    current_targets = {
        str(name).strip(): target
        for name, target in prerequisite_semantic_targets.items()
        if str(name).strip() and isinstance(target, Mapping)
    }
    # Historical closeouts retain their recorded full library worksheet. A
    # current role-typed transaction must opt into the explicit boundary below.
    if source_map.get("semantic_route_schema") != 2:
        return dict(current_targets)

    try:
        routes = EvidenceRouteSet.from_source_map(source_map)
    except ObligationRouteError as exc:
        raise ValueError("invalid typed source route surface: " + str(exc)) from exc

    raw_explicit = source_map.get("library_semantic_prerequisite_sources", {})
    if raw_explicit is None:
        raw_explicit = {}
    if not isinstance(raw_explicit, Mapping) or not all(
        isinstance(declaration, str)
        and declaration.strip()
        and isinstance(source_item, str)
        and source_item.strip()
        for declaration, source_item in raw_explicit.items()
    ):
        raise ValueError(
            "library_semantic_prerequisite_sources must map nonempty Lean "
            "declaration names to nonempty source-item ids"
        )
    explicit = {
        str(declaration).strip(): str(source_item).strip()
        for declaration, source_item in raw_explicit.items()
    }
    source_items = source_map_items_by_key(source_map)
    unknown_source_items = sorted(set(explicit.values()) - set(source_items))
    if unknown_source_items:
        raise ValueError(
            "library_semantic_prerequisite_sources names absent source items: "
            + ", ".join(unknown_source_items)
        )
    unknown_declarations = sorted(set(explicit) - set(current_targets))
    if unknown_declarations:
        raise ValueError(
            "library_semantic_prerequisite_sources names outside the current "
            "Lean prerequisite surface: "
            + ", ".join(unknown_declarations)
        )

    routed_library_roots = {
        declaration
        for route in routes.routes
        if route.route_kind is RouteKind.SOURCE_SEMANTIC_DECLARATION
        for declaration in route.semantic_declarations
        if declaration in current_targets
    }
    missing = sorted(routed_library_roots - set(explicit))
    if missing:
        raise ValueError(
            "current reusable source-semantic declaration(s) lack an explicit "
            "library_semantic_prerequisite_sources route: "
            + ", ".join(missing)
        )
    return {name: current_targets[name] for name in sorted(explicit)}


def _source_connection(
    paper_dir: Path,
    *,
    source_items: Mapping[str, Mapping[str, Any]],
    ledger_item: Mapping[str, Any],
    repository_root: Path,
    file_bytes_override: Mapping[Path, bytes | None] | None,
) -> dict[str, str]:
    """Validate one exact local source connection and derive its review input."""

    source_item_key = str(ledger_item.get("source_item") or "").strip()
    source_record = source_items.get(source_item_key)
    source_locator = ""
    if source_item_key and source_record is None:
        source_error = (
            f"registered source item `{source_item_key}` is absent from the statement map"
        )
        source_record = None
    elif source_record is not None:
        source_locator = str(source_record.get("source_location") or "not recorded")
        source_error = ""
    elif isinstance(ledger_item.get("source_anchor_evidence"), list):
        source_record = ledger_item
        source_locator = str(ledger_item.get("source_location") or "not recorded")
        source_error = ""
    else:
        source_error = "no explicit byte-pinned paper source connection is registered"

    source_input = ""
    source_digest = ""
    source_anchor_digest = ""
    source_state = ""
    corrected_target_review_sha256 = ""
    if source_record is not None and not source_error:
        source_error = source_anchor_file_error(
            paper_dir,
            source_record,
            repository_root=repository_root,
            file_bytes_override=file_bytes_override,
        )
        if not source_error:
            source_input, source_digest, source_error = source_semantic_input_bundle(
                source_record,
                require_context_roles=True,
            )
        if not source_error:
            _, source_anchor_digest, source_error = source_semantic_input_bundle(
                source_record,
                require_context_roles=True,
                include_approved_contexts=False,
            )
        if not source_error:
            source_state = LOCAL_SOURCE_CONNECTION_STATE
        if (
            not source_error
            and str(source_record.get("coverage_status") or "").strip()
            == "corrected_source_statement"
        ):
            corrected_target = source_record.get("corrected_target")
            if not isinstance(corrected_target, Mapping):
                source_error = "corrected source item has no corrected target record"
            else:
                corrected_target_review_sha256 = corrected_target_review_digest(
                    corrected_target
                )
    return {
        "source_item": source_item_key,
        "source_locator": source_locator,
        "verbatim_source_input": source_input,
        "source_input_bundle_sha256": source_digest,
        "source_anchor_bundle_sha256": source_anchor_digest,
        "corrected_target_review_sha256": corrected_target_review_sha256,
        "source_connection_error": source_error,
        "source_connection_state": source_state,
    }


def _approved_corrected_target_current(
    *,
    source_items: Mapping[str, Mapping[str, Any]],
    ledger_item: Mapping[str, Any],
) -> bool:
    """Check the correction disposition against the current map row.

    This is intentionally separate from raw-source matching: the archival
    bytes remain in the source bundle while the approval-pinned corrected
    target is a distinct, explicitly labeled acceptance basis.
    """

    source_item = str(ledger_item.get("source_item") or "").strip()
    source_record = source_items.get(source_item)
    judgment = str(ledger_item.get("judgment") or "").strip().lower()
    if not source_requires_approved_corrected_target(source_record):
        return judgment != APPROVED_CORRECTED_TARGET_MATCH
    if judgment != APPROVED_CORRECTED_TARGET_MATCH:
        return False
    if not isinstance(source_record, Mapping):
        return False
    target = source_record.get("corrected_target")
    if (
        not isinstance(target, Mapping)
        or target.get("archival_equivalence_claimed") is not False
    ):
        return False
    return corrected_target_screening_binding_is_current(ledger_item, target)


def reusable_semantic_prerequisite_ledger_bindings(
    paper_dir: Path,
    *,
    current_entries: Mapping[str, Mapping[str, Any]],
    existing_items: Mapping[str, Any],
    source_items: Mapping[str, Mapping[str, Any]],
    repository_root: Path,
    file_bytes_override: Mapping[Path, bytes | None] | None,
    target_protocol_field: str,
    target_protocol: str,
    prior_code_sha256_field: str,
    current_code_sha256_field: str,
    prior_target_sha256_field: str,
    current_target_sha256_field: str,
    additional_identity_field_pairs: tuple[tuple[str, str], ...] = (),
) -> dict[str, tuple[str, dict[str, str]]]:
    """Bind current declarations to exact prior judgments without names.

    The prior row's source route is re-resolved against current frozen bytes;
    the current row contributes only Lean-produced semantic identities.  The
    shared binder accepts a rename only when the source bundle and Lean meaning
    form a mutual one-to-one match.  Ambiguous matches remain unbound.
    """

    def reusable(
        prior: object, current: Mapping[str, Any]
    ) -> dict[str, str] | None:
        if not isinstance(prior, Mapping):
            return None
        source = _source_connection(
            paper_dir,
            source_items=source_items,
            ledger_item=prior,
            repository_root=repository_root,
            file_bytes_override=file_bytes_override,
        )
        if (
            source["source_connection_error"]
            or source["source_connection_state"]
            != LOCAL_SOURCE_CONNECTION_STATE
        ):
            return None
        candidate = dict(current)
        candidate["source_input_bundle_sha256"] = source[
            "source_input_bundle_sha256"
        ]
        candidate["source_anchor_bundle_sha256"] = source[
            "source_anchor_bundle_sha256"
        ]
        candidate["corrected_target_review_sha256"] = source[
            "corrected_target_review_sha256"
        ]
        return reusable_semantic_judgment(
            prior,
            candidate,
            target_protocol_field=target_protocol_field,
            target_protocol=target_protocol,
            prior_code_sha256_field=prior_code_sha256_field,
            current_code_sha256_field=current_code_sha256_field,
            prior_target_sha256_field=prior_target_sha256_field,
            current_target_sha256_field=current_target_sha256_field,
            additional_identity_field_pairs=additional_identity_field_pairs,
        )

    return unique_reusable_judgment_bindings(
        current_entries,
        existing_items,
        reusable_judgment=reusable,
    )


def normalized_semantic_prerequisite_ledger(
    *,
    paper_dir: Path,
    repository_root: Path,
    source_map: Mapping[str, Any],
    ledger: Mapping[str, Any],
    semantic_targets: Mapping[str, Mapping[str, Any]],
    label: str,
    declaration_field: str,
    prompt_version: str,
    target_protocol: str,
    row_target_protocol_field: str,
    row_target_sha256_field: str,
    row_code_sha256_field: str,
    file_bytes_override: Mapping[Path, bytes | None] | None = None,
) -> dict[str, Any]:
    """Return one current-route view of a complete prior review ledger.

    This is a pure projection: it never rewrites the saved ledger or creates a
    verdict.  Every current Lean row and every prior reviewer row must
    participate in one mutual one-to-one exact source-and-semantic match.
    """

    if (
        ledger.get("schema") != 1
        or str(ledger.get("paper") or "").strip() != paper_dir.name
        or str(ledger.get("prompt_version") or "").strip() != prompt_version
        or str(ledger.get("target_protocol") or "").strip() != target_protocol
    ):
        raise ValueError(f"{label} has stale container identity")
    raw_items = ledger.get("items")
    if not isinstance(raw_items, Mapping):
        raise ValueError(f"{label} has no item map")
    existing_items = {
        str(name).strip(): row
        for name, row in raw_items.items()
        if str(name).strip() and isinstance(row, Mapping)
    }
    if len(existing_items) != len(raw_items):
        raise ValueError(f"{label} contains a malformed row")
    current_entries = {
        str(name): {
            "elaborated_signature_sha256": str(
                target.get("elaborated_signature_sha256") or ""
            ).strip().lower(),
            row_target_sha256_field: str(
                target.get("display_sha256") or ""
            ).strip().lower(),
            # Graph-native rows carry an elaborated signature. The exact-target
            # fallback supports older reviewed ledgers; syntax-only fallback is
            # deliberately unavailable at this acceptance boundary.
            "current_declaration_code_sha256": "",
        }
        for name, target in semantic_targets.items()
        if str(name).strip() and isinstance(target, Mapping)
    }
    bindings = reusable_semantic_prerequisite_ledger_bindings(
        paper_dir,
        current_entries=current_entries,
        existing_items=existing_items,
        source_items=source_map_items_by_key(source_map),
        repository_root=repository_root,
        file_bytes_override=file_bytes_override,
        target_protocol_field=row_target_protocol_field,
        target_protocol=target_protocol,
        prior_code_sha256_field=row_code_sha256_field,
        current_code_sha256_field="current_declaration_code_sha256",
        prior_target_sha256_field=row_target_sha256_field,
        current_target_sha256_field=row_target_sha256_field,
    )
    used_prior = {prior_name for prior_name, _metadata in bindings.values()}
    if set(bindings) != set(current_entries) or used_prior != set(existing_items):
        raise ValueError(
            f"{label} does not form a complete one-to-one semantic binding to "
            "the current Lean denominator"
        )
    return {
        **dict(ledger),
        "items": {
            current_name: {
                **dict(existing_items[prior_name]),
                declaration_field: current_name,
            }
            for current_name, (prior_name, _metadata) in sorted(bindings.items())
        },
    }


def project_paper_semantic_prerequisites(
    paper_dir: Path,
    *,
    claim_semantic_targets: Mapping[str, Mapping[str, Any]],
    prerequisite_semantic_targets: Mapping[str, Mapping[str, Any]],
    semantic_target_errors: Mapping[str, str] | None = None,
    declaration_sources: Mapping[str, Mapping[str, Any]],
    source_map: Mapping[str, Any],
    ledger: Mapping[str, Any],
    repository_root: Path,
    file_bytes_override: Mapping[Path, bytes | None] | None,
    supporting_declarations_sha256_by_name: Mapping[str, str] | None = None,
) -> list[dict[str, Any]]:
    """Project the source-boundary review subset of a Lean dependency closure.

    ``prerequisite_semantic_targets`` is the complete Lean-owned dependency
    closure. The typed statement map selects the smaller subset that represents
    a source model or formula in its own right. The remaining closure is still
    elaborated and proof-checked, but has no synthetic standalone source-review
    row.
    """

    # Callers retain the complete current graph. Selection is declarative, not
    # inferred by following the graph from a result claim in Python.
    _ = claim_semantic_targets
    selected_targets = selected_paper_semantic_prerequisite_targets(
        source_map,
        prerequisite_semantic_targets,
    )
    names = set(selected_targets)
    source_items = source_map_items_by_key(source_map)
    target_errors = semantic_target_errors or {}
    ledger_items = _clean_mapping(ledger.get("items"))
    ledger_current = bool(
        ledger.get("schema") == PAPER_PREREQUISITE_SCHEMA
        and ledger.get("paper") == paper_dir.name
        and ledger.get("prompt_version") == PAPER_PREREQUISITE_PROMPT_VERSION
        and ledger.get("target_protocol") == PAPER_PREREQUISITE_TARGET_PROTOCOL
    )
    support_digests = supporting_declarations_sha256_by_name or {}
    current_review_entries: dict[str, dict[str, Any]] = {}
    for name in names:
        declaration = _clean_mapping(declaration_sources.get(name))
        target = _clean_mapping(selected_targets.get(name))
        current_review_entries[name] = {
            "elaborated_signature_sha256": str(
                target.get("elaborated_signature_sha256") or ""
            ).strip().lower(),
            "paper_semantic_target_sha256": str(
                target.get("display_sha256") or ""
            ).strip().lower(),
            "paper_declaration_sha256": str(
                declaration.get("paper_declaration_sha256") or ""
            ).strip().lower(),
            "semantic_supporting_declarations_sha256": str(
                support_digests.get(name) or ""
            ).strip().lower(),
        }
    bindings = (
        reusable_semantic_prerequisite_ledger_bindings(
            paper_dir,
            current_entries=current_review_entries,
            existing_items=ledger_items,
            source_items=source_items,
            repository_root=repository_root,
            file_bytes_override=file_bytes_override,
            target_protocol_field="paper_semantic_target_protocol",
            target_protocol=PAPER_PREREQUISITE_TARGET_PROTOCOL,
            prior_code_sha256_field="paper_declaration_sha256",
            current_code_sha256_field="paper_declaration_sha256",
            prior_target_sha256_field="paper_semantic_target_sha256",
            current_target_sha256_field="paper_semantic_target_sha256",
        )
        if ledger_current
        else {}
    )
    entries: list[dict[str, Any]] = []
    for name in sorted(names):
        declaration = _clean_mapping(declaration_sources.get(name))
        target = _clean_mapping(selected_targets.get(name))
        binding = bindings.get(name)
        prior_name = binding[0] if binding is not None else name
        raw = _clean_mapping(ledger_items.get(prior_name))
        source = _source_connection(
            paper_dir,
            source_items=source_items,
            ledger_item=raw,
            repository_root=repository_root,
            file_bytes_override=file_bytes_override,
        )
        target_text = str(target.get("display") or "").strip()
        target_digest = str(target.get("display_sha256") or "").strip().lower()
        semantic_identity = str(
            target.get("elaborated_signature_sha256") or ""
        ).strip().lower()
        target_error = str(target_errors.get(name) or "").strip()
        if not target_text and not target_error:
            target_error = "Lean did not produce a paper-prerequisite semantic target"
        judgment = str(raw.get("judgment") or "").strip().lower()
        current = bool(
            ledger_current
            and binding is not None
            and declaration
            and target_text
            and not target_error
            and not source["source_connection_error"]
            and judgment in _JUDGMENTS
            and _approved_corrected_target_current(
                source_items=source_items, ledger_item=raw
            )
            and source["source_connection_state"] == LOCAL_SOURCE_CONNECTION_STATE
        )
        if not declaration:
            status = "Lean retained a paper-local prerequisite with no exact source declaration"
        elif target_error:
            status = target_error
        elif not ledger_current:
            status = "paper-prerequisite semantic-review ledger is missing or stale"
        elif source["source_connection_error"]:
            status = source["source_connection_error"]
        elif not judgment:
            status = "source connection is registered; semantic judgment is pending"
        elif not current:
            status = "recorded paper-prerequisite semantic judgment is stale or incomplete"
        else:
            status = "current"
        entries.append(
            {
                **declaration,
                "lean_name": name,
                **source,
                "source_connection_display_only": False,
                "paper_semantic_target": target_text,
                "paper_semantic_target_sha256": target_digest,
                "elaborated_signature_sha256": semantic_identity,
                "paper_semantic_target_kind": str(
                    target.get("declaration_kind") or ""
                ).strip(),
                "paper_semantic_target_root_expanded": target.get("root_expanded"),
                "paper_semantic_target_error": target_error,
                "direct_paper_declarations": list(
                    target.get("direct_paper_declarations", ())
                ),
                "direct_library_declarations": list(
                    target.get("direct_library_declarations", ())
                ),
                "semantic_supporting_declarations_sha256": str(
                    support_digests.get(name) or ""
                ).strip().lower(),
                "semantic_judgment": judgment or "not recorded",
                "semantic_reason": str(raw.get("reason") or "").strip(),
                "semantic_current": current,
                "semantic_status": status,
            }
        )
    return entries


def _library_ledger_error(paper: str, ledger: Mapping[str, Any]) -> str:
    if ledger.get("schema") != LIBRARY_SEMANTIC_REVIEW_SCHEMA:
        return "library semantic-review ledger has an unsupported schema"
    if str(ledger.get("paper") or "").strip() != paper:
        return "library semantic-review ledger names a different paper"
    if (
        str(ledger.get("prompt_version") or "").strip()
        != REQUIRED_LLM_LIBRARY_SEMANTIC_REVIEW_PROMPT_VERSION
    ):
        return "library semantic-review ledger has a stale or missing prompt version"
    if (
        str(ledger.get("target_protocol") or "").strip()
        != LIBRARY_SEMANTIC_TARGET_PROTOCOL
    ):
        return "library semantic-review ledger has a stale or missing target protocol"
    return ""


def project_library_semantic_prerequisites(
    paper_dir: Path,
    *,
    semantic_targets: Mapping[str, Mapping[str, Any]],
    semantic_target_errors: Mapping[str, str],
    declaration_sources: Mapping[str, Mapping[str, Any]],
    source_map: Mapping[str, Any],
    ledger: Mapping[str, Any],
    repository_root: Path,
    file_bytes_override: Mapping[Path, bytes | None] | None,
    required_names: Iterable[str] = (),
    labels_by_name: Mapping[str, str] | None = None,
) -> list[dict[str, Any]]:
    """Project the source-mapped reusable-library review frontier.

    ``semantic_targets`` is Lean's complete reusable dependency closure. The
    source map selects the material reusable roots with actual source
    connections; all other rows remain graph-checked proof support and do not
    need a fabricated source-to-library verdict.
    """

    selected_targets = selected_library_semantic_prerequisite_targets(
        source_map,
        semantic_targets,
    )
    selected_errors = {
        str(name).strip(): str(error).strip()
        for name, error in semantic_target_errors.items()
        if str(name).strip()
        and str(error).strip()
        and str(name).strip() in selected_targets
    }
    extra_required_names = (
        required_names if source_map.get("semantic_route_schema") != 2 else ()
    )
    names = {
        str(name).strip()
        for name in (
            *selected_targets.keys(),
            *selected_errors.keys(),
            *extra_required_names,
        )
        if str(name).strip()
    }
    labels = labels_by_name or {}
    source_items = source_map_items_by_key(source_map)
    ledger_error = _library_ledger_error(paper_dir.name, ledger)
    ledger_items = _clean_mapping(ledger.get("items"))
    current_review_entries: dict[str, dict[str, Any]] = {}
    for name in names:
        target = _clean_mapping(selected_targets.get(name))
        declaration = _clean_mapping(declaration_sources.get(name))
        definition_digest = str(
            declaration.get("library_definition_sha256") or ""
        ).strip().lower()
        current_review_entries[name] = {
            "elaborated_signature_sha256": str(
                target.get("elaborated_signature_sha256") or ""
            ).strip().lower(),
            "library_semantic_target_sha256": str(
                target.get("display_sha256") or ""
            ).strip().lower(),
            "current_named_library_definition_sha256": str(
                declaration.get("current_named_library_definition_sha256")
                or definition_digest
            ).strip().lower(),
        }
    bindings = (
        reusable_semantic_prerequisite_ledger_bindings(
            paper_dir,
            current_entries=current_review_entries,
            existing_items=ledger_items,
            source_items=source_items,
            repository_root=repository_root,
            file_bytes_override=file_bytes_override,
            target_protocol_field="library_semantic_target_protocol",
            target_protocol=LIBRARY_SEMANTIC_TARGET_PROTOCOL,
            prior_code_sha256_field="library_definition_sha256",
            current_code_sha256_field="current_named_library_definition_sha256",
            prior_target_sha256_field="library_semantic_target_sha256",
            current_target_sha256_field="library_semantic_target_sha256",
        )
        if not ledger_error
        else {}
    )
    entries: list[dict[str, Any]] = []
    for name in sorted(names):
        target = _clean_mapping(selected_targets.get(name))
        declaration = _clean_mapping(declaration_sources.get(name))
        definition = str(declaration.get("library_definition") or "").strip()
        definition_digest = str(
            declaration.get("library_definition_sha256") or ""
        ).strip().lower()
        definition_path = str(declaration.get("library_source_path") or "").strip()
        line_start = declaration.get("library_line_start")
        line_end = declaration.get("library_line_end")
        definition_error = str(
            declaration.get("library_definition_error") or ""
        ).strip()
        if not definition or not _SHA256_RE.fullmatch(definition_digest):
            definition_error = definition_error or "Lean-owned library declaration source is incomplete"
        if not definition_path or not isinstance(line_start, int) or not isinstance(line_end, int):
            definition_error = definition_error or "Lean-owned library declaration source is incomplete"

        target_text = str(target.get("display") or "").strip()
        target_digest = str(target.get("display_sha256") or "").strip().lower()
        semantic_identity = str(
            target.get("elaborated_signature_sha256") or ""
        ).strip().lower()
        target_error = str(selected_errors.get(name) or "").strip()
        if not target_text and not target_error:
            target_error = "Lean produced no library semantic target"

        binding = bindings.get(name)
        prior_name = binding[0] if binding is not None else name
        raw = _clean_mapping(ledger_items.get(prior_name))
        source = _source_connection(
            paper_dir,
            source_items=source_items,
            ledger_item=raw,
            repository_root=repository_root,
            file_bytes_override=file_bytes_override,
        )
        current_named_digest = str(
            declaration.get("current_named_library_definition_sha256")
            or definition_digest
        ).strip().lower()
        judgment = str(raw.get("judgment") or "").strip().lower()
        current = bool(
            not ledger_error
            and binding is not None
            and not definition_error
            and not target_error
            and target_text
            and not source["source_connection_error"]
            and judgment in _JUDGMENTS
            and _approved_corrected_target_current(
                source_items=source_items, ledger_item=raw
            )
            and source["source_connection_state"] == LOCAL_SOURCE_CONNECTION_STATE
        )
        if ledger_error:
            status = ledger_error
        elif definition_error:
            status = definition_error
        elif target_error:
            status = target_error
        elif source["source_connection_error"]:
            status = source["source_connection_error"]
        elif not judgment:
            status = "source connection is registered; semantic judgment is pending"
        elif not current:
            status = "recorded library semantic judgment is stale or incomplete"
        else:
            status = "current"
        entries.append(
            {
                "lean_name": name,
                "label": str(labels.get(name) or raw.get("label") or name).strip(),
                "library_source_path": definition_path,
                "library_line_start": line_start,
                "library_line_end": line_end,
                "library_definition": definition,
                "library_definition_sha256": definition_digest,
                "current_named_library_definition_sha256": current_named_digest,
                "library_definition_error": definition_error,
                "library_semantic_target": target_text,
                "library_semantic_target_sha256": target_digest,
                "elaborated_signature_sha256": semantic_identity,
                "library_semantic_target_kind": str(
                    target.get("declaration_kind") or ""
                ).strip(),
                "library_semantic_target_error": target_error,
                "direct_library_declarations": list(
                    target.get("direct_library_declarations", ())
                ),
                **source,
                "source_connection_display_only": False,
                "semantic_judgment": judgment or "not recorded",
                "semantic_reason": str(raw.get("reason") or "").strip(),
                "semantic_current": current,
                "semantic_status": status,
            }
        )
    return entries
