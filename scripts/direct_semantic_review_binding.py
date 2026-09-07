"""Bind direct source-to-Spec judgments to current semantic claims.

This is the acceptance-neutral identity boundary shared by the review writer,
fresh graph materializer, and terminal verifier.  It compares the exact source
bundle and Lean's fully expanded semantic target, never declaration names,
source item keys, derived claim-role views, paths, or line coordinates.  Claim
manifests and atoms remain mandatory Lean-owned coverage diagnostics, but a
change to that derived presentation alone is not a new source-to-Lean semantic
claim for a reviewer to judge.  This module performs no Lean discovery,
rendering, judgment, or evidence issuance.
"""

from __future__ import annotations

import re
from collections.abc import Mapping
from pathlib import Path
from typing import Any

from scripts.corrected_target_identity import (
    CORRECTED_TARGET_REVIEW_PROTOCOL,
    LEGACY_CORRECTED_TARGET_REVIEW_PROTOCOL,
    corrected_target_review_digest,
)
from scripts.lean_signature_manifest import validated_review_claim_atom_material
from scripts.obligation_routes import EvidenceRouteSet
from scripts.semantic_review_binding import unique_reusable_judgment_bindings
from scripts.source_review_input import (
    source_anchor_file_error,
    source_semantic_input_bundle,
    statement_digest,
)
from scripts.v11_screening_contract import validate_v11_screening_container


SOURCE_INPUT_PROTOCOL = "verbatim_source_anchor_bundle_v1"
LEAN_TARGET_PROTOCOL = "lean_transparent_paper_expansion_with_claim_atoms_v2"
APPROVED_CORRECTED_TARGET_MATCH = "matches_approved_corrected_target"
_SHA256_RE = re.compile(r"[0-9a-f]{64}")


def direct_source_spec_semantic_identity_matches(
    prior: object,
    current: Mapping[str, Any],
) -> bool:
    """Compare source and expanded Lean identity, not derived diagnostics."""

    if not isinstance(prior, Mapping):
        return False
    expected = {
        "source_input_protocol": SOURCE_INPUT_PROTOCOL,
        "source_input_bundle_sha256": str(
            current.get("source_input_bundle_sha256") or ""
        ).strip().lower(),
        "paper_statement_sha256": str(
            current.get("paper_statement_sha256") or ""
        ).strip().lower(),
        "lean_target_protocol": str(
            current.get("lean_target_protocol") or ""
        ).strip(),
        "lean_expanded_statement_sha256": str(
            current.get("lean_expanded_statement_sha256") or ""
        ).strip().lower(),
    }
    return all(
        value and str(prior.get(field) or "").strip() == value
        for field, value in expected.items()
    )


def reusable_direct_source_spec_judgment(
    prior: object,
    current: Mapping[str, Any],
) -> dict[str, str] | None:
    """Return reviewer metadata only for the same source and Lean claim."""

    if not isinstance(prior, Mapping):
        return None
    coverage_status = str(current.get("coverage_status") or "").strip()
    expected_judgment = (
        APPROVED_CORRECTED_TARGET_MATCH
        if coverage_status == "corrected_source_statement"
        else "matches"
    )
    if (
        str(prior.get("judgment") or "").strip().lower() != expected_judgment
        or not str(prior.get("reason") or "").strip()
        or not direct_source_spec_semantic_identity_matches(prior, current)
    ):
        return None

    corrected_review = str(
        current.get("corrected_target_review_sha256") or ""
    ).strip().lower()
    corrected_record = str(
        current.get("corrected_target_sha256") or ""
    ).strip().lower()
    if expected_judgment == APPROVED_CORRECTED_TARGET_MATCH:
        protocol = str(prior.get("corrected_target_protocol") or "").strip()
        correction_current = (
            protocol == CORRECTED_TARGET_REVIEW_PROTOCOL
            and _SHA256_RE.fullmatch(corrected_review)
            and str(
                prior.get("corrected_target_review_sha256") or ""
            ).strip().lower()
            == corrected_review
        ) or (
            protocol == LEGACY_CORRECTED_TARGET_REVIEW_PROTOCOL
            and _SHA256_RE.fullmatch(corrected_record)
            and str(prior.get("corrected_target_sha256") or "").strip().lower()
            == corrected_record
        )
        if not correction_current:
            return None
    elif (
        str(prior.get("corrected_target_sha256") or "").strip()
        or str(prior.get("corrected_target_review_sha256") or "").strip()
    ):
        return None
    return {
        "judgment": expected_judgment,
        "reason": str(prior.get("reason") or "").strip(),
    }


def direct_current_identity_from_queue_context(
    *,
    declaration_context: Mapping[str, Any],
    source_context: Mapping[str, Any],
) -> dict[str, str]:
    """Flatten one writer queue card into the shared semantic identity."""

    identity = declaration_context.get("declaration_identity")
    if not isinstance(identity, Mapping):
        return {}
    approved = source_context.get("approved_corrected_target")
    return {
        "source_input_bundle_sha256": str(
            source_context.get("source_input_bundle_sha256") or ""
        ).strip().lower(),
        "paper_statement_sha256": statement_digest(
            str(source_context.get("verbatim_source_input") or "")
        ),
        "lean_target_protocol": str(
            identity.get("lean_target_protocol") or ""
        ).strip(),
        "lean_expanded_statement_sha256": str(
            identity.get("lean_expanded_statement_sha256") or ""
        ).strip().lower(),
        "coverage_status": str(identity.get("coverage_status") or "").strip(),
        "corrected_target_sha256": str(
            identity.get("corrected_target_sha256") or ""
        ).strip().lower(),
        "corrected_target_review_sha256": (
            str(approved.get("corrected_target_review_sha256") or "")
            .strip()
            .lower()
            if isinstance(approved, Mapping)
            else ""
        ),
    }


def _current_direct_identities(
    *,
    paper_dir: Path,
    source_map: Mapping[str, Any],
    route_set: EvidenceRouteSet,
    semantic_targets: Mapping[str, Mapping[str, Any]],
    repository_root: Path,
    file_bytes_override: Mapping[Path, bytes | None] | None,
) -> tuple[dict[str, dict[str, str]], dict[str, str]]:
    source_items = source_map.get("items")
    if not isinstance(source_items, Mapping):
        raise ValueError("paper statement map has no item map")
    routes = route_set.result_routes()
    expected_names = {route.spec_declaration for route in routes}
    if set(semantic_targets) != expected_names:
        raise ValueError(
            "current Lean semantic targets differ from the typed direct surface"
        )
    entries: dict[str, dict[str, str]] = {}
    source_items_by_name: dict[str, str] = {}
    for route in routes:
        name = route.spec_declaration
        source_item = route.source_item_id
        source_record = source_items.get(source_item)
        target = semantic_targets.get(name)
        if not isinstance(source_record, Mapping) or not isinstance(target, Mapping):
            raise ValueError(f"direct semantic material is incomplete: {name}")
        if (
            str(target.get("semantic_review_declaration") or name).strip()
            != route.semantic_review_declaration
        ):
            raise ValueError(
                f"{name}: Lean semantic target disagrees with its typed review route"
            )
        source_error = source_anchor_file_error(
            paper_dir,
            source_record,
            repository_root=repository_root,
            file_bytes_override=file_bytes_override,
        )
        if source_error:
            raise ValueError(f"{name}: exact source bundle is unavailable: {source_error}")
        source_text, source_digest, source_error = source_semantic_input_bundle(
            source_record,
            require_context_roles=True,
        )
        if source_error or not source_text or not _SHA256_RE.fullmatch(source_digest):
            raise ValueError(f"{name}: exact source bundle is incomplete")
        try:
            _atoms, atom_digest = validated_review_claim_atom_material(target)
        except ValueError as exc:
            raise ValueError(f"{name}: Lean claim atoms are invalid: {exc}") from exc
        manifest_digest = str(
            target.get("review_claim_manifest_sha256") or ""
        ).strip().lower()
        expanded_digest = str(target.get("display_sha256") or "").strip().lower()
        target_protocol = str(
            target.get("lean_target_protocol") or LEAN_TARGET_PROTOCOL
        ).strip()
        if (
            not _SHA256_RE.fullmatch(manifest_digest)
            or not _SHA256_RE.fullmatch(atom_digest)
            or not _SHA256_RE.fullmatch(expanded_digest)
            or not target_protocol
        ):
            raise ValueError(f"{name}: Lean claim identity is incomplete")
        corrected = source_record.get("corrected_target")
        entries[name] = {
            "source_input_bundle_sha256": source_digest,
            "paper_statement_sha256": statement_digest(source_text),
            "lean_target_protocol": target_protocol,
            "review_claim_manifest_sha256": manifest_digest,
            "review_claim_atoms_sha256": atom_digest,
            "lean_expanded_statement_sha256": expanded_digest,
            "coverage_status": str(
                source_record.get("coverage_status") or ""
            ).strip(),
            "corrected_target_sha256": (
                str(corrected.get("corrected_target_sha256") or "")
                .strip()
                .lower()
                if isinstance(corrected, Mapping)
                else ""
            ),
            "corrected_target_review_sha256": (
                corrected_target_review_digest(corrected)
                if isinstance(corrected, Mapping)
                else ""
            ),
        }
        source_items_by_name[name] = source_item
    return entries, source_items_by_name


def normalized_direct_screening_ledger(
    *,
    paper_dir: Path,
    source_map: Mapping[str, Any],
    screening: Mapping[str, Any],
    route_set: EvidenceRouteSet,
    semantic_targets: Mapping[str, Mapping[str, Any]],
    repository_root: Path,
    file_bytes_override: Mapping[Path, bytes | None] | None = None,
) -> dict[str, Any]:
    """Return a current-name view of one complete direct-review ledger.

    This pure projection creates no verdict and performs no write.  Current
    schema-3 rows may move only through a complete mutual one-to-one source and
    Lean claim match.  Historical schema-2 rows retain exact-name behavior.
    """

    items = screening.get("items")
    if not isinstance(items, Mapping):
        raise ValueError("v11 screening has no item map")
    if screening.get("schema") != 3:
        current_names = {
            route.semantic_review_declaration for route in route_set.result_routes()
        }
        if set(items) != current_names:
            raise ValueError(
                "legacy v11 screening cannot be rebound across declaration names"
            )
        return dict(screening)
    validation = validate_v11_screening_container(
        screening,
        paper=paper_dir.name,
    )
    if not validation.current:
        raise ValueError("; ".join(validation.errors))
    current, source_items_by_name = _current_direct_identities(
        paper_dir=paper_dir,
        source_map=source_map,
        route_set=route_set,
        semantic_targets=semantic_targets,
        repository_root=repository_root,
        file_bytes_override=file_bytes_override,
    )
    prior = {
        str(name).strip(): row
        for name, row in items.items()
        if str(name).strip() and isinstance(row, Mapping)
    }
    if len(prior) != len(items):
        raise ValueError("v11 screening contains a malformed row")
    bindings = unique_reusable_judgment_bindings(
        current,
        prior,
        reusable_judgment=reusable_direct_source_spec_judgment,
    )
    used_prior = {prior_name for prior_name, _metadata in bindings.values()}
    if set(bindings) != set(current) or used_prior != set(prior):
        raise ValueError(
            "v11 screening does not form a complete one-to-one semantic binding "
            "to the current direct Lean surface"
        )
    normalized_items: dict[str, dict[str, Any]] = {}
    routes_by_specification = route_set.result_route_by_specification()
    for current_name, (prior_name, _metadata) in sorted(bindings.items()):
        row = dict(prior[prior_name])
        row["source_item"] = source_items_by_name[current_name]
        row["semantic_target_declaration"] = current_name
        route = routes_by_specification[current_name]
        if route.semantic_review_declaration == current_name:
            row.pop("semantic_review_declaration", None)
        else:
            row["semantic_review_declaration"] = (
                route.semantic_review_declaration
            )
        normalized_items[current_name] = row
    return {**dict(screening), "items": normalized_items}
