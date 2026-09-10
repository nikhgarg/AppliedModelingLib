#!/usr/bin/env python3
"""Prepare a source-first v11 contract map without issuing semantic receipts.

This mechanical preparer is deliberately narrow.  It binds a curated list of
canonical paper claim Specs to existing byte-pinned source inventory items; it
does not judge their meanings, invent claim atoms, or make an older receipt
current.  The resulting map is therefore an auditable *pending* v11 surface:
every selected Spec has one source route, while any retained source claim with
no selected semantic target remains visible for the subsequent review.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import re
import sys
from collections.abc import Mapping
from pathlib import Path
from typing import Any

ROOT = Path(__file__).resolve().parents[1]
if __package__ in {None, ""}:
    repository_root = str(ROOT)
    if repository_root not in sys.path:
        sys.path.insert(0, repository_root)

from scripts.corrected_target_identity import (
    CORRECTED_TARGET_APPROVAL_PROTOCOL,
    CORRECTED_TARGET_ORIGINAL_ARTIFACT_PATH_FIELD,
    corrected_target_approval_artifact_error,
    corrected_target_original_artifact_path_error,
    corrected_target_record_digest,
    corrected_target_review_digest,
    normalize_approval_excerpt,
)
from scripts.formalization_protocol import (
    CLOSEOUT_REVIEW_POLICY_FIELD,
    CLOSEOUT_SOURCE_SCOPE_ALL_PROSE,
    FormalizationProtocolError,
    closeout_review_policy_material_projection,
    explicit_closeout_review_policy_from_source_map,
    resolve_closeout_review_policy,
)
from scripts.obligation_routes import (
    PROOF_CONTRACT_SOURCE_KINDS,
    SOURCE_SEMANTIC_DECLARATION_KINDS,
)
from scripts.source_coverage_scope import (
    SOURCE_PRESENTATION_ALIAS_EXPLICIT_RENUMBERED_RESTATEMENT,
    SOURCE_PRESENTATION_ALIAS_LABEL_RELATION_FIELD,
    SOURCE_PRESENTATION_ALIAS_RENUMBERED_EVIDENCE_FIELD,
    SOURCE_PRESENTATION_ALIAS_SAME_VISIBLE_LABEL,
    source_item_is_named_theoretical_statement,
)
from scripts.source_inventory_review import (
    SourceInventoryReviewError,
    materialize_prose_definition_presentations,
    materialize_source_named_result_inventory_review,
)
from scripts.source_named_result_index import (
    SOURCE_PRESENTATION_RECONCILIATION_BOUNDARY_REASONS,
)
from scripts.source_review_input import (
    APPROVED_REVIEW_CONTEXT_SCHEMA_FIELD,
    APPROVED_REVIEW_CONTEXTS_FIELD,
    SEMANTIC_CONTEXT_ROLES,
    SourceReviewInputError,
    canonical_source_anchor_evidence,
    materialize_approved_review_contexts,
)

_SOURCE_LOCATOR_RE = re.compile(r"^(?P<path>[^:]+):(?P<start>[1-9][0-9]*)(?:-(?P<end>[1-9][0-9]*))?$")


class PreparationError(ValueError):
    """Raised when a proposed source-to-Spec route is ambiguous or invalid."""


def _reject_duplicate_json_object_keys(
    pairs: list[tuple[str, object]],
) -> dict[str, object]:
    """Decode one JSON object without silently accepting shadowed fields."""

    result: dict[str, object] = {}
    for key, value in pairs:
        if key in result:
            raise ValueError(f"duplicate JSON object key `{key}`")
        result[key] = value
    return result


def load_object(path: Path, *, label: str) -> dict[str, Any]:
    try:
        payload = json.loads(
            path.read_text(encoding="utf-8"),
            object_pairs_hook=_reject_duplicate_json_object_keys,
        )
    except (OSError, json.JSONDecodeError, ValueError) as error:
        raise PreparationError(f"could not read {label}: {error}") from error
    if not isinstance(payload, dict):
        raise PreparationError(f"{label} must be a JSON object")
    return payload


def as_string_list(value: object, *, label: str) -> list[str]:
    if not isinstance(value, list) or not all(
        isinstance(item, str) and item.strip() for item in value
    ):
        raise PreparationError(f"{label} must be a list of nonempty strings")
    result = [item.strip() for item in value]
    if len(result) != len(set(result)):
        raise PreparationError(f"{label} must not contain duplicates")
    return result


def full_name(namespace: str, module: str, short: str) -> str:
    return f"{namespace}.{module}.{short}" if module else f"{namespace}.{short}"


def evidence_declaration_name(
    namespace: str, interface_module: str, spec: str, config: Mapping[str, Any]
) -> str:
    """Resolve one configured proof endpoint without forcing PaperInterface.

    A source-facing ``Spec`` belongs in PaperInterface, while its exact proof
    endpoint may deliberately live in a sibling ProofInterface.  A fully
    qualified configured endpoint is therefore authoritative; legacy short
    names retain the PaperInterface default.
    """

    raw = config.get("evidence_declaration_for_spec", {})
    if isinstance(raw, Mapping):
        candidate = str(raw.get(spec) or (spec + "Spec_proof")).strip()
    else:
        candidate = spec + "Spec_proof"
    if candidate.startswith(namespace + "."):
        return candidate
    return full_name(namespace, interface_module, candidate)


def _sha256_file(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as stream:
        for chunk in iter(lambda: stream.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def _source_quote(folder: Path, locator: str) -> tuple[str, str]:
    match = _SOURCE_LOCATOR_RE.fullmatch(locator.strip())
    if match is None:
        raise PreparationError(
            "corrected-target archival_source_locator must be one relative file:line or file:start-end anchor"
        )
    path = folder / match.group("path")
    try:
        relative = path.resolve().relative_to(folder.resolve())
    except ValueError as error:
        raise PreparationError("corrected-target source anchor leaves its paper folder") from error
    if not path.is_file() or str(relative).startswith("../"):
        raise PreparationError(f"corrected-target source anchor `{locator}` is not a readable paper-local file")
    text = path.read_text(encoding="utf-8").replace("\r\n", "\n").replace("\r", "\n")
    lines = text.split("\n")
    if text.endswith("\n"):
        lines.pop()
    start = int(match.group("start"))
    end = int(match.group("end") or start)
    if start > end or end > len(lines):
        raise PreparationError(f"corrected-target source anchor `{locator}` is out of range")
    quote = "\n".join(lines[start - 1 : end])
    return quote, hashlib.sha256(quote.encode("utf-8")).hexdigest()


def _validated_corrected_target_defect_ids(
    folder: Path, governing: list[str]
) -> list[str]:
    """Fail early when a corrected target has no current defect ledger route.

    The raw source-record audit deliberately requires both halves of a source
    correction: the source-map target and a source-proof defect explaining why
    the archival statement is not the checked target.  Validate that relation
    while preparing the map so a missing ledger cannot surface only after an
    expensive recursive raw audit.
    """

    ledger_path = folder / "audit" / "source_proof_fidelity.json"
    ledger = load_object(ledger_path, label="source-proof fidelity ledger")
    if ledger.get("paper") not in {None, folder.name}:
        raise PreparationError(
            "source-proof fidelity ledger paper does not match the prepared paper"
        )
    defects = ledger.get("defects")
    if not isinstance(defects, list):
        raise PreparationError("source-proof fidelity ledger defects must be a list")
    indexed: dict[str, Mapping[str, Any]] = {}
    for raw_defect in defects:
        if not isinstance(raw_defect, Mapping):
            continue
        defect_id = str(raw_defect.get("id") or "").strip()
        if not defect_id:
            continue
        if defect_id in indexed:
            raise PreparationError(
                f"source-proof fidelity ledger duplicates defect id `{defect_id}`"
            )
        indexed[defect_id] = raw_defect
    normalized = [value.strip() for value in governing]
    for defect_id in normalized:
        defect = indexed.get(defect_id)
        if defect is None:
            raise PreparationError(
                f"corrected target cites unknown source-proof defect `{defect_id}`"
            )
        if str(defect.get("resolution") or "").strip() != "corrected_source_statement":
            raise PreparationError(
                f"source-proof defect `{defect_id}` must resolve as corrected_source_statement"
            )
        if str(defect.get("statement_impact") or "").strip() != "source_statement":
            raise PreparationError(
                f"source-proof defect `{defect_id}` must have statement_impact source_statement"
            )
    return normalized


def _apply_corrected_targets(
    items: dict[str, dict[str, Any]],
    config: Mapping[str, Any],
    *,
    folder: Path | None,
) -> None:
    """Apply explicit approved-target records without deciding their semantics.

    This prepares the deterministic pins an independent reviewer needs.  It
    intentionally accepts neither an inferred correction nor a replacement of
    the archival statement: every target, defect id, source anchor, and
    approval reference must be supplied in the configuration.
    """

    raw_targets = config.get("corrected_targets", {})
    if raw_targets in ({}, None):
        return
    if folder is None:
        raise PreparationError("corrected_targets require the paper folder")
    if not isinstance(raw_targets, Mapping):
        raise PreparationError("corrected_targets must be an object keyed by source-map item")
    for raw_key, raw_target in raw_targets.items():
        key = str(raw_key).strip()
        if not key or key not in items or not isinstance(raw_target, Mapping):
            raise PreparationError("each corrected_targets entry needs an existing source-map item and object")
        statement = str(raw_target.get("statement") or "").strip()
        archival_statement = str(raw_target.get("archival_statement") or "").strip()
        locator = str(raw_target.get("archival_source_locator") or "").strip()
        source_note = str(raw_target.get("source_note") or "").strip()
        governing = raw_target.get("governing_defect_ids")
        approval_raw = raw_target.get("approval")
        if not statement or not archival_statement or not locator or not source_note:
            raise PreparationError(
                f"{key}: corrected target needs statement, archival_statement, archival_source_locator, and source_note"
            )
        if re.sub(r"\s+", " ", statement) == re.sub(r"\s+", " ", archival_statement):
            raise PreparationError(f"{key}: corrected target must differ from its preserved archival_statement")
        if (
            not isinstance(governing, list)
            or not governing
            or any(not isinstance(value, str) or not value.strip() for value in governing)
            or len({value.strip() for value in governing}) != len(governing)
        ):
            raise PreparationError(f"{key}: governing_defect_ids must be a nonempty unique string list")
        if not isinstance(approval_raw, Mapping):
            raise PreparationError(f"{key}: corrected target needs an approval object")
        kind = str(approval_raw.get("kind") or "").strip()
        recorded_at = str(approval_raw.get("recorded_at") or "").strip()
        reference = str(approval_raw.get("reference") or "").strip()
        artifact_rel = str(approval_raw.get("artifact_path") or "").strip()
        artifact_excerpt = normalize_approval_excerpt(
            approval_raw.get("artifact_excerpt")
        )
        artifact = folder / artifact_rel
        try:
            artifact.resolve().relative_to(folder.resolve())
        except ValueError as error:
            raise PreparationError(f"{key}: approval artifact must remain paper-local") from error
        if (
            not kind
            or not recorded_at
            or not reference
            or not artifact_rel
            or not artifact.is_file()
            or len(artifact_excerpt) < 40
        ):
            raise PreparationError(
                f"{key}: approval needs kind, recorded_at, reference, a readable "
                "paper-local artifact_path, and a substantive artifact_excerpt"
            )
        _quote, quote_digest = _source_quote(folder, locator)
        approval = {
            "kind": kind,
            "recorded_at": recorded_at,
            "reference": reference,
            "target_statement_sha256": hashlib.sha256(
                re.sub(r"\s+", " ", statement).strip().encode("utf-8")
            ).hexdigest(),
            "artifact_path": artifact_rel,
            "artifact_protocol": CORRECTED_TARGET_APPROVAL_PROTOCOL,
            "artifact_excerpt": artifact_excerpt,
            "artifact_excerpt_sha256": hashlib.sha256(
                artifact_excerpt.encode("utf-8")
            ).hexdigest(),
        }
        if CORRECTED_TARGET_ORIGINAL_ARTIFACT_PATH_FIELD in approval_raw:
            approval[CORRECTED_TARGET_ORIGINAL_ARTIFACT_PATH_FIELD] = approval_raw[
                CORRECTED_TARGET_ORIGINAL_ARTIFACT_PATH_FIELD
            ]
            original_path_error = corrected_target_original_artifact_path_error(
                approval
            )
            if original_path_error:
                raise PreparationError(f"{key}: approval {original_path_error}")
        try:
            artifact_text = artifact.read_text(encoding="utf-8")
        except (OSError, UnicodeError) as exc:
            raise PreparationError(
                f"{key}: approval artifact is not readable UTF-8 text"
            ) from exc
        approval_error = corrected_target_approval_artifact_error(
            approval, artifact_text
        )
        if approval_error:
            raise PreparationError(f"{key}: {approval_error}")
        validated_governing = _validated_corrected_target_defect_ids(
            folder, [value.strip() for value in governing]
        )
        target: dict[str, Any] = {
            "schema": 1,
            "statement": statement,
            "governing_defect_ids": validated_governing,
            "archival_equivalence_claimed": False,
            "archival_source_locator": locator,
            "archival_source_quote_sha256": quote_digest,
            "approval": approval,
        }
        target["corrected_target_review_sha256"] = corrected_target_review_digest(
            target
        )
        target["corrected_target_sha256"] = corrected_target_record_digest(target)
        item = items[key]
        existing_defect_ids = item.get("source_defect_ids", [])
        if not isinstance(existing_defect_ids, list) or any(
            not isinstance(value, str) or not value.strip()
            for value in existing_defect_ids
        ):
            raise PreparationError(
                f"{key}: existing source_defect_ids must be a string list"
            )
        source_defect_ids = list(
            dict.fromkeys(
                [
                    *(value.strip() for value in existing_defect_ids),
                    *validated_governing,
                ]
            )
        )
        item["coverage_status"] = "corrected_source_statement"
        item["source_status"] = "corrected"
        item["inventory_role"] = "corrected_source_target"
        item["statement"] = archival_statement
        item["source_note"] = source_note
        # A source presentation can also carry a local proof typo or another
        # defect that does not govern this corrected statement.  Applying the
        # corrected target must not erase those independently reviewed links.
        item["source_defect_ids"] = source_defect_ids
        item["corrected_target"] = target


def _apply_selected_item_dispositions(
    items: dict[str, dict[str, Any]],
    config: Mapping[str, Any],
    selected_by_item: Mapping[str, str],
) -> None:
    """Materialize configured non-archival dispositions on selected rows.

    A source map is itself the input to a clean semantic review. Keeping a
    finite-replacement disposition solely in preparation configuration makes
    that review depend on an implicit side channel. This helper places the
    configured classification and its reason on the generated source row;
    approved corrected targets are subsequently allowed to replace this
    provisional status with their stricter correction record.
    """

    raw_dispositions = config.get("selected_item_dispositions", {})
    if raw_dispositions in ({}, None):
        return
    if not isinstance(raw_dispositions, Mapping):
        raise PreparationError("selected_item_dispositions must be an object")
    for raw_key, raw_value in raw_dispositions.items():
        key = str(raw_key).strip()
        if not key or key not in items or not isinstance(raw_value, Mapping):
            raise PreparationError(
                "each selected_item_dispositions entry needs an existing source-map item and object"
            )
        if key not in selected_by_item:
            raise PreparationError(
                f"{key}: selected_item_dispositions may only classify a selected source item"
            )
        source_status = str(raw_value.get("source_status") or "").strip()
        coverage_status = str(raw_value.get("coverage_status") or "").strip()
        reason = str(raw_value.get("reason") or "").strip()
        archival_equivalence_claimed = raw_value.get("archival_equivalence_claimed")
        if not source_status or not coverage_status or not reason:
            raise PreparationError(
                f"{key}: selected disposition needs source_status, coverage_status, and reason"
            )
        if not isinstance(archival_equivalence_claimed, bool):
            raise PreparationError(
                f"{key}: selected disposition needs boolean archival_equivalence_claimed"
            )
        item = items[key]
        item["source_status"] = source_status
        item["coverage_status"] = coverage_status
        item["archival_equivalence_claimed"] = archival_equivalence_claimed
        existing_note = str(item.get("source_note") or "").strip()
        disposition_note = f"Formalization disposition: {reason}"
        # Preparation may be rerun against a previously materialized map.
        # Replace, rather than append to, the prior generated disposition so
        # the canonical map is byte-stable under that normal workflow.
        generated_marker = " Formalization disposition: "
        if existing_note.startswith("Formalization disposition: "):
            existing_note = ""
        elif generated_marker in existing_note:
            existing_note = existing_note.split(generated_marker, maxsplit=1)[0]
        item["source_note"] = (
            f"{existing_note} {disposition_note}" if existing_note else disposition_note
        )


def _upgrade_legacy_corrected_target_approval_artifacts(
    items: Mapping[str, dict[str, Any]],
    config: Mapping[str, Any],
    *,
    folder: Path | None,
) -> None:
    """Promote an explicit legacy correction memo to the current narrow pin.

    Older maps can already have an approved corrected mathematical target but
    retain only a whole-file approval hash.  That is insufficient for a fresh
    reviewer: it cannot see the exact authority selecting the repaired target.
    A migration configuration therefore supplies one explicit, unique excerpt
    per paper-local memo.  This routine changes neither the archival source
    nor the corrected mathematical statement; it merely makes the existing
    approval authoritative under the current reviewer-input protocol.
    """

    raw_upgrades = config.get("legacy_corrected_target_approval_artifacts", {})
    if raw_upgrades in ({}, None):
        return
    if folder is None:
        raise PreparationError(
            "legacy corrected-target approval upgrades require the paper folder"
        )
    if not isinstance(raw_upgrades, Mapping):
        raise PreparationError(
            "legacy_corrected_target_approval_artifacts must be an object"
        )
    for raw_path, raw_plan in raw_upgrades.items():
        artifact_path = str(raw_path).strip()
        if not artifact_path or not isinstance(raw_plan, Mapping):
            raise PreparationError(
                "each legacy corrected-target approval upgrade needs an artifact path and object"
            )
        excerpt = normalize_approval_excerpt(raw_plan.get("artifact_excerpt"))
        artifact = folder / artifact_path
        try:
            artifact.resolve().relative_to(folder.resolve())
        except ValueError as error:
            raise PreparationError(
                "legacy corrected-target approval artifact must remain paper-local"
            ) from error
        if not artifact.is_file() or len(excerpt) < 40:
            raise PreparationError(
                "legacy corrected-target approval upgrade needs a readable artifact and substantive artifact_excerpt"
            )
        try:
            artifact_text = artifact.read_text(encoding="utf-8")
        except (OSError, UnicodeError) as error:
            raise PreparationError(
                "legacy corrected-target approval artifact is not readable UTF-8 text"
            ) from error
        approval_excerpt_sha256 = hashlib.sha256(excerpt.encode("utf-8")).hexdigest()
        probe = {
            "artifact_protocol": CORRECTED_TARGET_APPROVAL_PROTOCOL,
            "artifact_excerpt": excerpt,
            "artifact_excerpt_sha256": approval_excerpt_sha256,
        }
        artifact_error = corrected_target_approval_artifact_error(probe, artifact_text)
        if artifact_error:
            raise PreparationError(
                f"legacy corrected-target approval `{artifact_path}`: {artifact_error}"
            )
        matched = 0
        for key, item in items.items():
            if str(item.get("coverage_status") or "").strip() != "corrected_source_statement":
                continue
            target = item.get("corrected_target")
            if not isinstance(target, dict):
                continue
            prior_approval = target.get("approval")
            if not isinstance(prior_approval, Mapping) or str(
                prior_approval.get("artifact_path") or ""
            ).strip() != artifact_path:
                continue
            matched += 1
            protocol = str(prior_approval.get("artifact_protocol") or "").strip()
            if protocol == CORRECTED_TARGET_APPROVAL_PROTOCOL:
                continue
            if protocol:
                raise PreparationError(
                    f"{key}: legacy corrected-target approval has an unknown protocol `{protocol}`"
                )
            statement = str(target.get("statement") or "").strip()
            kind = str(prior_approval.get("kind") or "").strip()
            recorded_at = str(prior_approval.get("recorded_at") or "").strip()
            reference = str(prior_approval.get("reference") or "").strip()
            governing = target.get("governing_defect_ids")
            if (
                not statement
                or not kind
                or not recorded_at
                or not reference
                or not isinstance(governing, list)
                or not governing
                or any(not isinstance(value, str) or not value.strip() for value in governing)
                or target.get("archival_equivalence_claimed") is not False
                or not str(item.get("source_note") or "").strip()
            ):
                raise PreparationError(
                    f"{key}: legacy corrected target lacks a complete existing correction record"
                )
            _validated_corrected_target_defect_ids(
                folder, [value.strip() for value in governing]
            )
            target["approval"] = {
                "kind": kind,
                "recorded_at": recorded_at,
                "reference": reference,
                "target_statement_sha256": hashlib.sha256(
                    re.sub(r"\s+", " ", statement).strip().encode("utf-8")
                ).hexdigest(),
                "artifact_path": artifact_path,
                "artifact_protocol": CORRECTED_TARGET_APPROVAL_PROTOCOL,
                "artifact_excerpt": excerpt,
                "artifact_excerpt_sha256": approval_excerpt_sha256,
            }
            target["corrected_target_review_sha256"] = corrected_target_review_digest(
                target
            )
            target["corrected_target_sha256"] = corrected_target_record_digest(target)
        if not matched:
            raise PreparationError(
                f"legacy corrected-target approval `{artifact_path}` did not match a legacy corrected target"
            )


def _apply_legacy_semantic_context_roles(
    items: Mapping[str, dict[str, Any]], config: Mapping[str, Any]
) -> None:
    """Assign explicit current roles to legacy contextual source excerpts.

    Earlier maps retained useful source context with a descriptive ``kind``
    but no reviewer-facing semantic role.  The migration configuration must
    classify every such context; this helper never guesses from its prose or
    declaration name.  It preserves the legacy kind and explanation because
    those carry useful human navigation.
    """

    raw_roles = config.get("legacy_semantic_context_roles", {})
    if raw_roles in ({}, None):
        return
    if not isinstance(raw_roles, Mapping):
        raise PreparationError("legacy_semantic_context_roles must be an object")
    for raw_key, raw_kind_roles in raw_roles.items():
        key = str(raw_key).strip()
        contexts = items.get(key, {}).get("semantic_context_requirements")
        if (
            not key
            or not isinstance(contexts, list)
            or not contexts
            or not isinstance(raw_kind_roles, Mapping)
        ):
            raise PreparationError(
                "each legacy semantic-context role entry needs an existing item, contexts, and kind-to-role object"
            )
        kind_roles = {
            str(raw_kind).strip(): str(raw_role).strip()
            for raw_kind, raw_role in raw_kind_roles.items()
        }
        if (
            not kind_roles
            or any(not kind or role not in SEMANTIC_CONTEXT_ROLES for kind, role in kind_roles.items())
        ):
            raise PreparationError(
                f"{key}: legacy semantic-context roles need nonempty kinds and permitted roles"
            )
        missing_kinds: set[str] = set()
        for index, context in enumerate(contexts):
            if not isinstance(context, dict):
                raise PreparationError(
                    f"{key}: semantic_context_requirements[{index}] is not an object"
                )
            role = str(context.get("semantic_role") or "").strip()
            if role:
                if role not in SEMANTIC_CONTEXT_ROLES:
                    raise PreparationError(
                        f"{key}: semantic_context_requirements[{index}] has an unknown semantic_role"
                    )
                continue
            kind = str(context.get("kind") or "").strip()
            configured_role = kind_roles.get(kind)
            if configured_role is None:
                missing_kinds.add(kind or f"context[{index}] without kind")
                continue
            context["semantic_role"] = configured_role
        if missing_kinds:
            raise PreparationError(
                f"{key}: legacy semantic contexts lack configured roles for "
                + ", ".join(sorted(missing_kinds))
            )


def _initialize_selected_source_claim_atoms(
    items: Mapping[str, dict[str, Any]],
    selected_by_item: Mapping[str, str],
    config: Mapping[str, Any],
    *,
    namespace: str,
    interface_module: str,
    enabled: object,
) -> bool:
    """Pin one already-curated source claim to its exact existing anchor.

    Legacy source maps frequently predate the v11 atom schema while already
    containing one curated source statement and one exact quote bundle per
    direct source item.  This is a mechanical schema migration only: it uses
    that existing statement verbatim, refuses ambiguous multi-anchor items,
    and records the already selected paper-interface proof route.  It never
    derives an atom from a Lean declaration name.
    """

    if enabled in {None, False}:
        return False
    if enabled is not True:
        raise PreparationError("initialize_selected_source_claim_atoms must be boolean")
    for key, spec in selected_by_item.items():
        item = items[key]
        existing = item.get("source_claim_atoms")
        if existing is not None and existing != []:
            if (
                isinstance(existing, list)
                and len(existing) == 1
                and isinstance(existing[0], dict)
                and existing[0].get("id") == key.replace("_", ".")
            ):
                # This is the deterministic initialization record from an
                # earlier invocation.  Keep its source semantics and quote
                # pin but rebind the route if the interface layout changed.
                existing[0]["reviewed_lean_route"] = evidence_declaration_name(
                    namespace, interface_module, spec, config
                )
            continue
        statement = str(item.get("statement") or "").strip()
        # A source-only curator may have already pinned one completed
        # statement core inside a deliberately broader coverage span.  The
        # source atom is the identity of the direct semantic comparison, so it
        # must use that exact core rather than re-expanding the reviewer
        # surface to surrounding proof or explanatory text.  A malformed
        # curated core fails closed; it must not silently fall back to the
        # broad historical bundle.
        semantic_anchors = item.get("semantic_source_anchor_evidence")
        if semantic_anchors is not None:
            if not isinstance(semantic_anchors, list) or len(semantic_anchors) != 1:
                raise PreparationError(
                    f"{key}: semantic_source_anchor_evidence must contain one exact source anchor"
                )
            anchors = semantic_anchors
        else:
            anchors = item.get("source_anchor_evidence")
        if not statement or not isinstance(anchors, list) or len(anchors) != 1:
            raise PreparationError(
                f"{key}: atom initialization needs one existing substantive statement and exact source anchor"
            )
        anchor = anchors[0]
        if not isinstance(anchor, Mapping):
            raise PreparationError(f"{key}: existing source anchor must be an object")
        path = str(anchor.get("path") or "").strip()
        start = anchor.get("line_start")
        end = anchor.get("line_end")
        quote_digest = str(anchor.get("quoted_text_sha256") or "").strip()
        if (
            not path
            or not isinstance(start, int)
            or isinstance(start, bool)
            or not isinstance(end, int)
            or isinstance(end, bool)
            or start < 1
            or end < start
            or not re.fullmatch(r"[0-9a-fA-F]{64}", quote_digest)
        ):
            raise PreparationError(f"{key}: existing source anchor is not a byte-pinned file span")
        item["source_claim_atoms"] = [
            {
                "id": key.replace("_", "."),
                "source_locator": f"{path}:{start}-{end}",
                "semantic_claim": statement,
                "reviewed_lean_route": evidence_declaration_name(
                    namespace, interface_module, spec, config
                ),
                "source_quote_sha256": quote_digest.lower(),
                "identity_schema": 2,
            }
        ]
    return True


def _apply_explicit_source_claim_atoms(
    items: Mapping[str, dict[str, Any]],
    selected_by_item: Mapping[str, str],
    config: Mapping[str, Any],
    *,
    folder: Path | None,
    namespace: str,
    interface_module: str,
) -> None:
    """Install reviewed one-anchor atoms for selected multi-span presentations.

    The ordinary initializer intentionally accepts only a source item with one
    anchor.  A source theorem can, however, have one statement span and a
    separately pinned proof or model-context span.  This migration-only input
    records which *one* exact statement anchor owns the source claim instead
    of letting a mechanical tool choose one from a multi-span presentation.
    """

    raw_atoms = config.get("explicit_source_claim_atoms", {})
    if raw_atoms in ({}, None):
        return
    if folder is None:
        raise PreparationError("explicit_source_claim_atoms require the paper folder")
    if not isinstance(raw_atoms, Mapping):
        raise PreparationError("explicit_source_claim_atoms must be an object")
    for raw_key, raw_atom_group in raw_atoms.items():
        key = str(raw_key).strip()
        if key not in selected_by_item:
            raise PreparationError(
                "each explicit_source_claim_atoms entry needs a selected source item"
            )
        if isinstance(raw_atom_group, Mapping):
            atom_group = [raw_atom_group]
        elif isinstance(raw_atom_group, list) and raw_atom_group and all(
            isinstance(atom, Mapping) for atom in raw_atom_group
        ):
            atom_group = raw_atom_group
        else:
            raise PreparationError(
                f"{key}: explicit source claim atoms must be one object or a nonempty object list"
            )
        spec = selected_by_item[key]
        prepared_atoms: list[dict[str, Any]] = []
        atom_ids: set[str] = set()
        for raw_atom in atom_group:
            atom_id = str(raw_atom.get("id") or "").strip()
            locator = str(raw_atom.get("source_locator") or "").strip()
            claim = str(raw_atom.get("semantic_claim") or "").strip()
            if not atom_id or not locator or not claim:
                raise PreparationError(
                    f"{key}: each explicit source claim atom needs id, source_locator, and semantic_claim"
                )
            if atom_id in atom_ids:
                raise PreparationError(
                    f"{key}: explicit source claim atom ids must be unique"
                )
            atom_ids.add(atom_id)
            anchors = _canonical_anchor_evidence(folder, locator)
            if len(anchors) != 1:
                raise PreparationError(
                    f"{key}: each explicit source claim atom must have one exact source anchor"
                )
            raw_clause = raw_atom.get("verbatim_source_clause")
            if len(atom_group) > 1 and (
                not isinstance(raw_clause, str) or not raw_clause.strip()
            ):
                raise PreparationError(
                    f"{key}: each atom in a multi-clause source presentation needs "
                    "one verbatim_source_clause"
                )
            if raw_clause is not None and not isinstance(raw_clause, str):
                raise PreparationError(
                    f"{key}: verbatim_source_clause must be a string when present"
                )
            anchor_quote = str(anchors[0]["quoted_text"])
            clause = str(raw_clause) if raw_clause is not None else ""
            if clause and anchor_quote.count(clause) != 1:
                raise PreparationError(
                    f"{key}: verbatim_source_clause must occur exactly once in its "
                    "exact source anchor"
                )
            prepared_atom = {
                "id": atom_id,
                "source_locator": locator,
                "source_quote_sha256": anchors[0]["quoted_text_sha256"],
                "semantic_claim": claim,
                "reviewed_lean_route": evidence_declaration_name(
                    namespace, interface_module, spec, config
                ),
                "identity_schema": 3 if clause else 2,
            }
            if clause:
                prepared_atom["verbatim_source_clause"] = clause
            prepared_atoms.append(prepared_atom)
        items[key]["source_claim_atoms"] = prepared_atoms


def _atomize_source_items(
    items: dict[str, dict[str, Any]], config: Mapping[str, Any]
) -> None:
    """Split an explicitly compound source presentation into claim-level rows.

    A v11 source-to-Spec contract is deliberately one-to-one.  Some earlier
    inventories used one source item for multiple separately stated branches
    of a displayed definition.  This helper preserves the same byte-pinned
    source anchor but requires the migration configuration to supply each
    branch's statement, source note, and direct Lean route.  It does not infer
    a semantic split from declaration names.
    """

    raw_atomizations = config.get("atomize_source_items", {})
    if raw_atomizations in ({}, None):
        return
    if not isinstance(raw_atomizations, Mapping):
        raise PreparationError("atomize_source_items must be an object")
    for raw_parent, raw_plan in raw_atomizations.items():
        parent = str(raw_parent).strip()
        if not parent or not isinstance(raw_plan, Mapping):
            raise PreparationError(
                "each atomize_source_items entry needs a source item name and object"
            )
        reason = str(raw_plan.get("reason") or "").strip()
        raw_atoms = raw_plan.get("items")
        if not reason or not isinstance(raw_atoms, Mapping) or not raw_atoms:
            raise PreparationError(
                f"{parent}: atomization needs a reason and nonempty items object"
            )
        atom_names = [str(raw_name).strip() for raw_name in raw_atoms]
        if (
            any(not name for name in atom_names)
            or len(atom_names) != len(set(atom_names))
        ):
            raise PreparationError(
                f"{parent}: atomized item names must be new, nonempty, and unique"
            )
        def configured_atom_fields(
            name: str, raw_atom: object, *, _parent: str = parent
        ) -> tuple[str, str, list[str], list[str] | None]:
            if not isinstance(raw_atom, Mapping):
                raise PreparationError(f"{_parent}/{name}: atom must be an object")
            statement = str(raw_atom.get("statement") or "").strip()
            source_note = str(raw_atom.get("source_note") or "").strip()
            declarations = raw_atom.get("lean_declarations")
            if (
                not statement
                or not source_note
                or not isinstance(declarations, list)
                or not declarations
                or any(
                    not isinstance(value, str) or not value.strip()
                    for value in declarations
                )
                or len({value.strip() for value in declarations}) != len(declarations)
            ):
                raise PreparationError(
                    f"{_parent}/{name}: atom needs statement, source_note, and unique lean_declarations"
                )
            defect_ids = raw_atom.get("source_defect_ids")
            if defect_ids is not None and (
                not isinstance(defect_ids, list)
                or not defect_ids
                or any(
                    not isinstance(value, str) or not value.strip()
                    for value in defect_ids
                )
                or len({value.strip() for value in defect_ids}) != len(defect_ids)
            ):
                raise PreparationError(
                    f"{_parent}/{name}: source_defect_ids must be a nonempty unique string list"
                )
            return (
                statement,
                source_note,
                [value.strip() for value in declarations],
                None
                if defect_ids is None
                else [value.strip() for value in defect_ids],
            )

        if parent not in items:
            # A prior invocation may already have replaced the compound
            # parent by every requested child.  Treat that exact state as an
            # idempotent success, but refuse a partially materialized split:
            # continuing from it could silently discard source inventory.
            if all(name in items for name in atom_names):
                for name in atom_names:
                    child = items[name]
                    statement, source_note, declarations, defect_ids = (
                        configured_atom_fields(name, raw_atoms[name])
                    )
                    child["statement"] = statement
                    child["source_note"] = source_note
                    child["lean_declarations"] = declarations
                    child["aliases"] = [
                        value.rsplit(".", maxsplit=1)[-1] for value in declarations
                    ]
                    if defect_ids is None:
                        child.pop("source_defect_ids", None)
                    else:
                        child["source_defect_ids"] = defect_ids
                    atomization = child.get("source_atomization")
                    if (
                        isinstance(atomization, Mapping)
                        and atomization.get("parent_source_item") == parent
                    ):
                        child.pop("inventory_role", None)
                        child.pop("scope_disposition", None)
                        child.pop("scope_disposition_note", None)
                continue
            if any(name in items for name in atom_names):
                raise PreparationError(
                    f"{parent}: source atomization is only partially materialized"
                )
            raise PreparationError(
                f"{parent}: source item is absent and no atomized children exist"
            )
        if any(name in items and name != parent for name in atom_names):
            raise PreparationError(
                f"{parent}: atomized item names must be new, nonempty, and unique"
            )
        original = items.pop(parent)
        for raw_name, raw_atom in raw_atoms.items():
            name = str(raw_name).strip()
            statement, source_note, declarations, defect_ids = configured_atom_fields(
                name, raw_atom
            )
            item = dict(original)
            item["statement"] = statement
            item["source_note"] = source_note
            item["lean_declarations"] = declarations
            item["aliases"] = [value.rsplit(".", maxsplit=1)[-1] for value in declarations]
            if defect_ids is not None:
                item["source_defect_ids"] = defect_ids
            # A previous preparation can have marked the compound parent as
            # pending source-claim atomization.  Once this configuration
            # splits it into claim-level children, that parent-only
            # disposition must not silently follow each selected result.
            item.pop("inventory_role", None)
            item.pop("scope_disposition", None)
            item.pop("scope_disposition_note", None)
            # The old reconciliation spoke about the compound presentation;
            # fresh v11 source-to-Spec review is responsible for the new
            # claim-level semantic comparison.
            item.pop("source_prose_definition_reconciliation", None)
            item["source_atomization"] = {
                "schema": 1,
                "parent_source_item": parent,
                "basis": reason,
                "validator": "v11 source-first review-surface preparation",
                "validated_at": "2026-08-18T00:00:00Z",
            }
            items[name] = item


def _deduplicated_values(values: list[object]) -> list[object]:
    """Preserve order while deduplicating JSON-shaped source metadata."""

    seen: set[str] = set()
    result: list[object] = []
    for value in values:
        token = json.dumps(value, ensure_ascii=True, sort_keys=True, separators=(",", ":"))
        if token not in seen:
            seen.add(token)
            result.append(value)
    return result


def _deduplicate_source_bundles(items: Mapping[str, dict[str, Any]]) -> None:
    """Normalize exact duplicate anchors and locator tokens repository-wide.

    A source-map migration can inherit duplicated anchors from an older
    preparer, a hand-curated bundle, or a context row re-materialized by the
    current configuration.  Exact repetition carries no additional source
    meaning, but it changes bundle hashes and therefore creates avoidable
    semantic-ledger churn.  Normalize every retained item after all merge
    operations rather than special-casing one migration shape.
    """

    for item in items.values():
        anchors = item.get("source_anchor_evidence")
        if isinstance(anchors, list):
            item["source_anchor_evidence"] = _deduplicated_values(anchors)
        location = item.get("source_location")
        if not isinstance(location, str):
            continue
        parts = [part.strip() for part in location.split(";") if part.strip()]
        item["source_location"] = "; ".join(
            str(part) for part in _deduplicated_values(parts)
        )


def _reclassify_source_item_kinds(
    items: Mapping[str, dict[str, Any]], config: Mapping[str, Any]
) -> None:
    """Apply a reviewed source-inventory kind correction before role routing.

    A source-only inventory can initially label a mathematically substantive
    conclusion as a ``remark`` because of its surrounding typography. Role
    schema 2 must classify the presentation by what the source claim is, not
    by that label. Keep this narrow, explicit, and idempotent: the
    preparation config names both the expected old and reviewed new kind, and
    rerunning after materialization accepts the new kind unchanged.
    """

    raw_reclassifications = config.get("reclassify_source_item_kinds", {})
    if raw_reclassifications in ({}, None):
        return
    if not isinstance(raw_reclassifications, Mapping):
        raise PreparationError("reclassify_source_item_kinds must be an object")
    for raw_name, raw_plan in raw_reclassifications.items():
        name = str(raw_name).strip()
        if not name or name not in items or not isinstance(raw_plan, Mapping):
            raise PreparationError(
                "each reclassify_source_item_kinds entry needs an existing item and object"
            )
        from_kind = str(raw_plan.get("from_kind") or "").strip().lower()
        to_kind = str(raw_plan.get("to_kind") or "").strip().lower()
        reason = str(raw_plan.get("reason") or "").strip()
        if not from_kind or not to_kind or not reason:
            raise PreparationError(
                f"{name}: source-kind reclassification needs from_kind, to_kind, and reason"
            )
        actual_kind = str(items[name].get("source_kind") or "").strip().lower()
        if actual_kind not in {from_kind, to_kind}:
            raise PreparationError(
                f"{name}: source-kind reclassification expected {from_kind!r} or "
                f"{to_kind!r}, found {actual_kind!r}"
            )
        items[name]["source_kind"] = to_kind


def _canonical_anchor_evidence(folder: Path, source_location: str) -> list[dict[str, Any]]:
    """Compatibility wrapper around the one source-anchor constructor."""

    try:
        return canonical_source_anchor_evidence(folder, source_location)
    except SourceReviewInputError as error:
        raise PreparationError(str(error)) from error


def _anchor_locator(anchor: Mapping[str, Any], *, label: str) -> str:
    """Recover the typed paper-local locator already owned by one anchor.

    Existing semantic-context records predate a separate ``source_location``
    field.  Their path and line coordinates are nevertheless the stable,
    semantic part of the source selection; quoted text and its digest are only
    derived bytes.  Reconstructing the locator from those coordinates lets the
    preparer refresh current bytes without inventing or broadening a source
    span.
    """

    path = str(anchor.get("path") or "").strip()
    start = anchor.get("line_start")
    end = anchor.get("line_end")
    if (
        not path
        or not isinstance(start, int)
        or isinstance(start, bool)
        or not isinstance(end, int)
        or isinstance(end, bool)
        or start < 1
        or end < start
    ):
        raise PreparationError(f"{label} lacks a valid paper-local path and line range")
    return f"{path}:{start}-{end}"


def _refresh_anchor_bundle(
    folder: Path, anchors: object, *, label: str
) -> list[dict[str, Any]]:
    """Refresh only the bytes of an already selected exact anchor bundle."""

    if not isinstance(anchors, list) or not anchors:
        raise PreparationError(f"{label} has no exact source-anchor bundle")
    refreshed: list[dict[str, Any]] = []
    for index, raw_anchor in enumerate(anchors):
        if not isinstance(raw_anchor, Mapping):
            raise PreparationError(f"{label}[{index}] is not an object")
        materialized = _canonical_anchor_evidence(
            folder,
            _anchor_locator(raw_anchor, label=f"{label}[{index}]"),
        )
        if len(materialized) != 1:
            raise PreparationError(f"{label}[{index}] is not one exact source span")
        refreshed.append(materialized[0])
    return refreshed


def _refresh_current_source_pins(
    items: Mapping[str, dict[str, Any]], *, folder: Path | None
) -> None:
    """Refresh mechanical byte pins after all source-inventory surgery.

    The preparation config and retained map own source locations, semantic
    claims, context roles, and reviewer judgments.  Quotes and quote digests
    are deterministic projections of those locations.  Refreshing those
    projections once, at the end of preparation and before inventory
    validation, prevents a canonical source correction from forcing hand
    edits to every embedded copy while preserving the exact review surface.
    """

    if folder is None:
        return
    for item_id, item in items.items():
        anchors = item.get("source_anchor_evidence")
        source_location = str(item.get("source_location") or "").strip()
        if anchors is not None:
            try:
                item["source_anchor_evidence"] = _refresh_anchor_bundle(
                    folder, anchors, label=f"{item_id}.source_anchor_evidence"
                )
            except PreparationError:
                # Legacy preparation fixtures may carry placeholder evidence
                # rather than a materializable anchor bundle.  Retain the
                # established location-derived fallback in that case.
                if not source_location:
                    raise
                item["source_anchor_evidence"] = _canonical_anchor_evidence(
                    folder, source_location
                )
        else:
            if source_location:
                item["source_anchor_evidence"] = _canonical_anchor_evidence(
                    folder, source_location
                )

        semantic_anchors = item.get("semantic_source_anchor_evidence")
        if semantic_anchors is not None:
            item["semantic_source_anchor_evidence"] = _refresh_anchor_bundle(
                folder,
                semantic_anchors,
                label=f"{item_id}.semantic_source_anchor_evidence",
            )

        contexts = item.get("semantic_context_requirements")
        if contexts is not None:
            if not isinstance(contexts, list):
                raise PreparationError(
                    f"{item_id}: semantic_context_requirements must be a list"
                )
            refreshed_contexts: list[dict[str, Any]] = []
            for index, raw_context in enumerate(contexts):
                if not isinstance(raw_context, Mapping):
                    raise PreparationError(
                        f"{item_id}: semantic_context_requirements[{index}] is not an object"
                    )
                context = dict(raw_context)
                context["source_anchor_evidence"] = _refresh_anchor_bundle(
                    folder,
                    context.get("source_anchor_evidence"),
                    label=(
                        f"{item_id}.semantic_context_requirements[{index}]"
                        ".source_anchor_evidence"
                    ),
                )
                refreshed_contexts.append(context)
            item["semantic_context_requirements"] = _deduplicated_values(
                refreshed_contexts
            )

        atoms = item.get("source_claim_atoms")
        if atoms is not None:
            if not isinstance(atoms, list):
                raise PreparationError(f"{item_id}: source_claim_atoms must be a list")
            refreshed_atoms: list[dict[str, Any]] = []
            for index, raw_atom in enumerate(atoms):
                if not isinstance(raw_atom, Mapping):
                    raise PreparationError(
                        f"{item_id}: source_claim_atoms[{index}] is not an object"
                    )
                atom = dict(raw_atom)
                locator = str(atom.get("source_locator") or "").strip()
                if not locator:
                    raise PreparationError(
                        f"{item_id}: source_claim_atoms[{index}] has no source_locator"
                    )
                anchors = _canonical_anchor_evidence(folder, locator)
                if len(anchors) != 1:
                    raise PreparationError(
                        f"{item_id}: source_claim_atoms[{index}] must select one exact source span"
                    )
                clause = atom.get("verbatim_source_clause")
                if clause is not None:
                    if not isinstance(clause, str) or not clause.strip():
                        raise PreparationError(
                            f"{item_id}: source_claim_atoms[{index}] has an invalid "
                            "verbatim_source_clause"
                        )
                    if str(anchors[0]["quoted_text"]).count(clause) != 1:
                        raise PreparationError(
                            f"{item_id}: source_claim_atoms[{index}] verbatim_source_clause "
                            "does not occur exactly once in the current exact source anchor"
                        )
                atom["source_quote_sha256"] = anchors[0]["quoted_text_sha256"]
                refreshed_atoms.append(atom)
            item["source_claim_atoms"] = refreshed_atoms


def _consolidate_source_items(
    items: dict[str, dict[str, Any]], config: Mapping[str, Any], *, folder: Path | None
) -> None:
    """Replace a prior implementation-level split by one paper-source claim.

    This is the inverse of atomization for the distinct case where the paper
    itself has one numbered/defined claim but the initial interface split its
    semantic content into several Specs.  The configuration must spell out the
    one source presentation, exact semantic target, and one atom; this helper
    only performs deterministic inventory surgery and exact source pinning.
    """

    raw_consolidations = config.get("consolidate_source_items", {})
    if raw_consolidations in ({}, None):
        return
    if folder is None:
        raise PreparationError("consolidate_source_items require the paper folder")
    if not isinstance(raw_consolidations, Mapping):
        raise PreparationError("consolidate_source_items must be an object")
    for raw_name, raw_plan in raw_consolidations.items():
        name = str(raw_name).strip()
        if not name or not isinstance(raw_plan, Mapping):
            raise PreparationError("each consolidated source item needs a name and object")
        raw_sources = raw_plan.get("source_items")
        if not isinstance(raw_sources, list) or len(raw_sources) < 2:
            raise PreparationError(f"{name}: source_items must name at least two prior source items")
        sources = [str(value).strip() for value in raw_sources]
        if any(not value for value in sources) or len(sources) != len(set(sources)):
            raise PreparationError(f"{name}: source_items must be nonempty and unique")
        target_already_exists = name in items
        if target_already_exists and any(source in items for source in sources):
            raise PreparationError(f"{name}: target already exists while prior source items remain")
        missing = [source for source in sources if source not in items]
        if missing and not target_already_exists:
            raise PreparationError(f"{name}: source item(s) absent: {', '.join(missing)}")
        statement = str(raw_plan.get("statement") or "").strip()
        source_note = str(raw_plan.get("source_note") or "").strip()
        source_kind = str(raw_plan.get("source_kind") or "").strip()
        source_location = str(raw_plan.get("source_location") or "").strip()
        declarations = raw_plan.get("lean_declarations")
        raw_atom = raw_plan.get("source_claim_atom")
        if (
            not statement
            or not source_note
            or not source_kind
            or not source_location
            or not isinstance(declarations, list)
            or len(declarations) != 1
            or not isinstance(declarations[0], str)
            or not declarations[0].strip()
            or not isinstance(raw_atom, Mapping)
        ):
            raise PreparationError(
                f"{name}: needs statement, source_note, source_kind, source_location, "
                "one lean declaration, and source_claim_atom"
            )
        atom_id = str(raw_atom.get("id") or "").strip()
        atom_locator = str(raw_atom.get("source_locator") or "").strip()
        atom_claim = str(raw_atom.get("semantic_claim") or "").strip()
        if not atom_id or not atom_locator or not atom_claim:
            raise PreparationError(
                f"{name}: source_claim_atom needs id, source_locator, and semantic_claim"
            )
        atom_anchors = _canonical_anchor_evidence(folder, atom_locator)
        if len(atom_anchors) != 1:
            raise PreparationError(
                f"{name}: source_claim_atom.source_locator must be one exact source anchor"
            )
        source_items = [items.pop(name)] if target_already_exists else [items.pop(source) for source in sources]
        result = dict(source_items[0])
        result["statement"] = statement
        result["source_note"] = source_note
        result["source_kind"] = source_kind
        result["source_location"] = source_location
        result["source_anchor_evidence"] = _canonical_anchor_evidence(folder, source_location)
        result["lean_declarations"] = [declarations[0].strip()]
        result["aliases"] = [declarations[0].strip().rsplit(".", maxsplit=1)[-1]]
        result["claim_bearing"] = True
        result["source_claim_atoms"] = [
            {
                "id": atom_id,
                "source_locator": atom_locator,
                "source_quote_sha256": atom_anchors[0]["quoted_text_sha256"],
                "semantic_claim": atom_claim,
                "reviewed_lean_route": declarations[0].strip() + "Spec",
            }
        ]
        raw_reconciliation = raw_plan.get("prose_definition_reconciliation")
        if raw_reconciliation is not None:
            if not isinstance(raw_reconciliation, Mapping) or source_kind != "definition":
                raise PreparationError(
                    f"{name}: prose_definition_reconciliation is allowed only for a definition object"
                )
            presentation_sha = str(raw_reconciliation.get("presentation_sha256") or "").strip()
            semantic_basis = str(raw_reconciliation.get("semantic_basis") or "").strip()
            validator = str(raw_reconciliation.get("validator") or "").strip()
            validator_type = str(raw_reconciliation.get("validator_type") or "").strip()
            validated_at = str(raw_reconciliation.get("validated_at") or "").strip()
            if (
                not re.fullmatch(r"[0-9a-fA-F]{64}", presentation_sha)
                or len(semantic_basis) < 20
                or not validator
                or validator_type not in {"agent", "human", "model"}
                or not validated_at
            ):
                raise PreparationError(
                    f"{name}: prose_definition_reconciliation needs a presentation SHA-256, "
                    "substantive basis, validator, validator type, and timestamp"
                )
            statement_digest = hashlib.sha256(
                " ".join(statement.replace("\r\n", "\n").replace("\r", "\n").split()).encode("utf-8")
            ).hexdigest()
            result["source_prose_definition_reconciliation"] = {
                "schema": 2,
                "relation": "source_item_represents_prose_definition",
                "presentation_sha256": presentation_sha.lower(),
                "source_item_statement_sha256": statement_digest,
                "judgment": "semantically_equivalent",
                "semantic_basis": semantic_basis,
                "validator": validator,
                "validator_type": validator_type,
                "validated_at": validated_at,
            }
        raw_contexts = raw_plan.get("semantic_context_requirements")
        clear_contexts = raw_plan.get("clear_semantic_context_requirements")
        if clear_contexts is True:
            if raw_contexts is not None:
                raise PreparationError(
                    f"{name}: cannot supply and clear semantic_context_requirements"
                )
            contexts = []
        elif clear_contexts not in {None, False}:
            raise PreparationError(
                f"{name}: clear_semantic_context_requirements must be boolean"
            )
        elif raw_contexts is None:
            contexts = _deduplicated_values(
                [
                    context
                    for source in source_items
                    for context in source.get("semantic_context_requirements", [])
                    if isinstance(context, Mapping)
                ]
            )
        else:
            if not isinstance(raw_contexts, list) or not raw_contexts:
                raise PreparationError(
                    f"{name}: semantic_context_requirements must be a nonempty list when supplied"
                )
            contexts = []
            for index, raw_context in enumerate(raw_contexts):
                if not isinstance(raw_context, Mapping):
                    raise PreparationError(
                        f"{name}: semantic_context_requirements[{index}] must be an object"
                    )
                semantic_role = str(raw_context.get("semantic_role") or "").strip()
                context_location = str(raw_context.get("source_location") or "").strip()
                if semantic_role not in {
                    "definition",
                    "model",
                    "model_construction",
                    "scope",
                    "prior_result",
                    "stated_antecedent",
                } or not context_location:
                    raise PreparationError(
                        f"{name}: semantic context needs a bounded semantic_role and source_location"
                    )
                context: dict[str, Any] = {
                    "semantic_role": semantic_role,
                    "source_anchor_evidence": _canonical_anchor_evidence(
                        folder, context_location
                    ),
                }
                contexts.append(context)
            contexts = _deduplicated_values(contexts)
        if contexts:
            result["semantic_context_requirements"] = contexts
        else:
            result.pop("semantic_context_requirements", None)
        conventions = _deduplicated_values(
            [
                convention
                for source in source_items
                for convention in source.get("model_convention_ids", [])
                if isinstance(convention, str) and convention.strip()
            ]
        )
        if conventions:
            result["model_convention_ids"] = conventions
        else:
            result.pop("model_convention_ids", None)
        raw_presentation_core = raw_plan.get("source_presentation_reconciliation")
        # A consolidation changes the owned source span.  A statement-core
        # reconciliation copied from one of the prior split rows is therefore
        # stale and would incorrectly make coverage exclusive to that old
        # core.  Preserve one only when the consolidation plan explicitly
        # supplies the replacement relation for the new combined owner.
        if raw_presentation_core is None:
            result.pop("source_presentation_reconciliation", None)
        if raw_presentation_core is not None:
            if not isinstance(raw_presentation_core, Mapping):
                raise PreparationError(
                    f"{name}: source_presentation_reconciliation must be an object"
                )
            presentation_kind = str(raw_presentation_core.get("presentation_kind") or "").strip()
            presentation_label = str(raw_presentation_core.get("presentation_label") or "").strip()
            core_locator = str(raw_presentation_core.get("core_anchor_locator") or "").strip()
            boundary_reason = str(raw_presentation_core.get("boundary_reason") or "").strip()
            semantic_basis = str(raw_presentation_core.get("semantic_basis") or "").strip()
            validator = str(raw_presentation_core.get("validator") or "").strip()
            validated_at = str(raw_presentation_core.get("validated_at") or "").strip()
            core_anchors = _canonical_anchor_evidence(folder, core_locator) if core_locator else []
            if (
                not presentation_kind
                or not presentation_label
                or len(core_anchors) != 1
                or boundary_reason
                not in SOURCE_PRESENTATION_RECONCILIATION_BOUNDARY_REASONS
                or not semantic_basis
                or not validator
                or not validated_at
            ):
                raise PreparationError(
                    f"{name}: source_presentation_reconciliation needs source kind/label, one core "
                    "anchor, supported boundary reason, basis, validator, and timestamp"
                )
            result["source_presentation_reconciliation"] = {
                "schema": 1,
                "relation": "conservative_text_span_core",
                "presentation_kind": presentation_kind,
                "presentation_label": presentation_label,
                "core_anchor": core_anchors[0],
                "boundary_reason": boundary_reason,
                "semantic_basis": semantic_basis,
                "validator": validator,
                "validated_at": validated_at,
            }
        for stale in (
            "source_atomization",
            "source_presentation_alias",
            "semantic_contract",
            "proof_lean_declarations",
            "support_lean_declarations",
            "source_spec_correspondence",
        ):
            result.pop(stale, None)
        items[name] = result


def _consolidate_presentation_aliases(
    items: dict[str, dict[str, Any]], config: Mapping[str, Any], *, folder: Path | None
) -> None:
    """Collapse redundant aliases of one repeated source presentation."""

    raw_consolidations = config.get("consolidate_presentation_aliases", {})
    if raw_consolidations in ({}, None):
        return
    if folder is None:
        raise PreparationError("consolidate_presentation_aliases require the paper folder")
    if not isinstance(raw_consolidations, Mapping):
        raise PreparationError("consolidate_presentation_aliases must be an object")
    for raw_name, raw_plan in raw_consolidations.items():
        name = str(raw_name).strip()
        if not name or not isinstance(raw_plan, Mapping):
            raise PreparationError("each consolidated presentation alias needs a name and object")
        raw_sources = raw_plan.get("source_items")
        if not isinstance(raw_sources, list) or len(raw_sources) < 2:
            raise PreparationError(f"{name}: source_items must name at least two prior aliases")
        sources = [str(value).strip() for value in raw_sources]
        if any(not value for value in sources) or len(sources) != len(set(sources)):
            raise PreparationError(f"{name}: source_items must be nonempty and unique")
        if name in items:
            if any(source in items for source in sources):
                raise PreparationError(f"{name}: target already exists while prior aliases remain")
            continue
        missing = [source for source in sources if source not in items]
        if missing:
            raise PreparationError(f"{name}: source alias(es) absent: {', '.join(missing)}")
        statement = str(raw_plan.get("statement") or "").strip()
        source_note = str(raw_plan.get("source_note") or "").strip()
        source_kind = str(raw_plan.get("source_kind") or "").strip()
        source_location = str(raw_plan.get("source_location") or "").strip()
        if not statement or not source_note or not source_kind or not source_location:
            raise PreparationError(
                f"{name}: needs statement, source_note, source_kind, and source_location"
            )
        prior_items = [items.pop(source) for source in sources]
        result = dict(prior_items[0])
        result["statement"] = statement
        result["source_note"] = source_note
        result["source_kind"] = source_kind
        result["source_location"] = source_location
        result["source_anchor_evidence"] = _canonical_anchor_evidence(folder, source_location)
        result["claim_bearing"] = False
        result["inventory_role"] = "source_presentation_alias"
        for stale in (
            "aliases",
            "lean_declarations",
            "proof_lean_declarations",
            "support_lean_declarations",
            "source_claim_atoms",
            "source_atomization",
            "source_spec_correspondence",
            "semantic_contract",
        ):
            result.pop(stale, None)
        items[name] = result


def _retire_non_source_items(
    items: dict[str, dict[str, Any]], config: Mapping[str, Any]
) -> None:
    """Remove a legacy audit row that is not its own source presentation.

    The source map is a source inventory, not a record of every helpful Lean
    bridge ever added during a formalization.  A v11 migration may therefore
    retire an old duplicated presentation row or an implementation-only bridge
    after its actual named source result is retained elsewhere.  The permanent
    preparation configuration must identify that retained source item and
    state why the retired row is not an independent source presentation.
    """

    raw_retirements = config.get("retire_non_source_items", {})
    if raw_retirements in ({}, None):
        return
    if not isinstance(raw_retirements, Mapping):
        raise PreparationError("retire_non_source_items must be an object")
    pending: list[tuple[str, str, str, str]] = []
    valid_kinds = {"legacy_duplicate_presentation", "formalization_bridge"}
    for raw_key, raw_plan in raw_retirements.items():
        key = str(raw_key).strip()
        if not key or not isinstance(raw_plan, Mapping):
            raise PreparationError(
                "each retire_non_source_items entry needs an existing item and object"
            )
        kind = str(raw_plan.get("kind") or "").strip()
        replacement = str(raw_plan.get("replacement_source_item") or "").strip()
        reason = str(raw_plan.get("reason") or "").strip()
        if kind not in valid_kinds or not replacement or len(reason) < 20:
            raise PreparationError(
                f"{key}: retirement needs a recognized kind, replacement_source_item, and substantive reason"
            )
        if replacement == key:
            raise PreparationError(f"{key}: retirement replacement cannot be the retired item")
        pending.append((key, kind, replacement, reason))
    for key, _kind, replacement, _reason in pending:
        if key not in items:
            # A prior deterministic run has already removed the non-source
            # bookkeeping row.  Requiring its replacement below still guards
            # against an accidental config copied into a different inventory.
            if replacement not in items:
                raise PreparationError(
                    f"{key}: retired item and replacement `{replacement}` are both absent"
                )
            continue
        if replacement not in items:
            raise PreparationError(
                f"{key}: replacement source item `{replacement}` is absent"
            )
        items.pop(key)


def _add_source_items(
    items: dict[str, dict[str, Any]], config: Mapping[str, Any], *, folder: Path | None
) -> None:
    """Add an explicitly reviewed source-inventory row during a v11 migration.

    Older maps sometimes omitted a source definition or a named proof-support
    lemma altogether.  This helper requires the migration configuration to
    state the source presentation and exact anchor; it only materializes that
    supplied inventory record and never infers it from a Lean declaration.
    """

    raw_additions = config.get("add_source_items", {})
    if raw_additions in ({}, None):
        return
    if folder is None:
        raise PreparationError("add_source_items require the paper folder")
    if not isinstance(raw_additions, Mapping):
        raise PreparationError("add_source_items must be an object")
    for raw_key, raw_item in raw_additions.items():
        key = str(raw_key).strip()
        if not key or not isinstance(raw_item, Mapping):
            raise PreparationError("each add_source_items entry needs a new item name and object")
        statement = str(raw_item.get("statement") or "").strip()
        source_kind = str(raw_item.get("source_kind") or "").strip()
        source_location = str(raw_item.get("source_location") or "").strip()
        source_note = str(raw_item.get("source_note") or "").strip()
        claim_bearing = raw_item.get("claim_bearing", True)
        source_status = str(raw_item.get("source_status") or "").strip()
        declarations = raw_item.get("lean_declarations", [])
        support = raw_item.get("support_lean_declarations", [])
        standard_term_interpretation = raw_item.get(
            "source_standard_term_interpretation"
        )
        # A migration may need to make a previously omitted named source claim
        # visible *before* it has a transparent Spec.  That is an explicit
        # pending claim, not proof support, so it deliberately has no Lean
        # route until the interface work is done.
        pending_unrouted_claim = (
            claim_bearing is True
            and source_status.lower() == "formalization_pending"
        )
        convention_ids = raw_item.get("model_convention_ids")
        source_defect_ids = raw_item.get("source_defect_ids")
        cited_source_artifact_id = str(
            raw_item.get("cited_source_artifact_id") or ""
        ).strip()
        cited_source_role = str(raw_item.get("cited_source_role") or "").strip()
        if (
            not statement
            or not source_kind
            or not source_location
            or not source_note
            or not isinstance(claim_bearing, bool)
            or not isinstance(declarations, list)
            or not isinstance(support, list)
            or any(not isinstance(value, str) or not value.strip() for value in declarations)
            or any(not isinstance(value, str) or not value.strip() for value in support)
            or (
                standard_term_interpretation is not None
                and not isinstance(standard_term_interpretation, Mapping)
            )
            or (not declarations and not support and not pending_unrouted_claim)
            or bool(cited_source_artifact_id) != bool(cited_source_role)
        ):
            raise PreparationError(
                f"{key}: added source item needs statement, source_kind, source_location, source_note, "
                "a Boolean claim_bearing, and at least one Lean or support declaration "
                "unless it is an explicit claim-bearing formalization_pending item"
            )
        if convention_ids is not None:
            convention_ids = as_string_list(
                convention_ids, label=f"{key}.model_convention_ids"
            )
        if source_defect_ids is not None:
            source_defect_ids = as_string_list(
                source_defect_ids, label=f"{key}.source_defect_ids"
            )
            if not source_defect_ids:
                raise PreparationError(
                    f"{key}.source_defect_ids must be nonempty when configured"
                )
        if key in items:
            # The curator-owned preparation config remains authoritative for
            # source metadata on a deterministic rerun. Preserve the map's
            # transformed semantic contracts and declaration routes, but
            # refresh the explicitly configured source span through the sole
            # byte-pinned anchor constructor.
            item = items[key]
            item["source_kind"] = source_kind
            item["source_location"] = source_location
            item["statement"] = statement
            item["source_note"] = source_note
            item["claim_bearing"] = claim_bearing
            item["source_anchor_evidence"] = _canonical_anchor_evidence(
                folder, source_location
            )
            if source_status:
                item["source_status"] = source_status
            else:
                item.pop("source_status", None)
            if convention_ids is not None:
                item["model_convention_ids"] = convention_ids
            if source_defect_ids is not None:
                item["source_defect_ids"] = source_defect_ids
            if standard_term_interpretation is not None:
                item["source_standard_term_interpretation"] = dict(
                    standard_term_interpretation
                )
            if cited_source_artifact_id:
                item["cited_source_artifact_id"] = cited_source_artifact_id
                item["cited_source_role"] = cited_source_role
            else:
                item.pop("cited_source_artifact_id", None)
                item.pop("cited_source_role", None)
            if source_status.lower() == "support_only" and support:
                # The preparation configuration is the curator-owned route
                # for an explicitly support-only presentation.  Refresh that
                # route on deterministic reruns instead of retaining a
                # discovery-era declaration guess from the prior map.
                item["support_lean_declarations"] = [
                    value.strip() for value in support
                ]
            continue
        item: dict[str, Any] = {
            "source_kind": source_kind,
            "source_location": source_location,
            "statement": statement,
            "source_note": source_note,
            "claim_bearing": claim_bearing,
            "source_anchor_evidence": _canonical_anchor_evidence(folder, source_location),
        }
        if declarations:
            item["lean_declarations"] = [value.strip() for value in declarations]
            item["aliases"] = [value.strip().rsplit(".", maxsplit=1)[-1] for value in declarations]
        if support:
            item["support_lean_declarations"] = [value.strip() for value in support]
        if source_status:
            item["source_status"] = source_status
        if convention_ids is not None:
            item["model_convention_ids"] = convention_ids
        if source_defect_ids is not None:
            item["source_defect_ids"] = source_defect_ids
        if standard_term_interpretation is not None:
            item["source_standard_term_interpretation"] = dict(
                standard_term_interpretation
            )
        if cited_source_artifact_id:
            item["cited_source_artifact_id"] = cited_source_artifact_id
            item["cited_source_role"] = cited_source_role
        items[key] = item


def _apply_approved_review_contexts(
    items: Mapping[str, dict[str, Any]], *, folder: Path | None
) -> None:
    """Project settled maintainer decisions into the exact reviewer bundle."""

    needs_ledger = any("model_convention_ids" in item for item in items.values())
    ledger: Mapping[str, Any] | None = None
    if needs_ledger:
        if folder is None:
            raise PreparationError("model_convention_ids require the paper folder")
        ledger = load_object(
            folder / "audit" / "source_proof_fidelity.json",
            label="source-proof fidelity ledger",
        )
    for key, item in items.items():
        contexts, error = materialize_approved_review_contexts(
            item, source_proof_fidelity=ledger
        )
        if error:
            raise PreparationError(f"{key}: {error}")
        if contexts:
            item[APPROVED_REVIEW_CONTEXT_SCHEMA_FIELD] = 1
            item[APPROVED_REVIEW_CONTEXTS_FIELD] = contexts
        else:
            item.pop(APPROVED_REVIEW_CONTEXT_SCHEMA_FIELD, None)
            item.pop(APPROVED_REVIEW_CONTEXTS_FIELD, None)


def _apply_model_convention_routes(
    items: Mapping[str, dict[str, Any]], config: Mapping[str, Any]
) -> None:
    """Install explicit source-item-to-settled-reading routes from config."""

    raw_routes = config.get("model_convention_ids_by_source_item", {})
    if not isinstance(raw_routes, Mapping):
        raise PreparationError(
            "model_convention_ids_by_source_item must be an object"
        )
    for raw_key, raw_ids in raw_routes.items():
        key = str(raw_key).strip()
        convention_ids = as_string_list(
            raw_ids,
            label=f"model_convention_ids_by_source_item.{key}",
        )
        if not key or key not in items:
            raise PreparationError(
                "each model_convention_ids_by_source_item entry needs an "
                "existing source item"
            )
        items[key]["model_convention_ids"] = convention_ids


def _replace_source_item_anchors(
    items: Mapping[str, dict[str, Any]], config: Mapping[str, Any], *, folder: Path | None
) -> None:
    """Replace a legacy broad source bundle with reviewed exact presentation spans."""

    raw_replacements = config.get("replace_source_item_anchors", {})
    if raw_replacements in ({}, None):
        return
    if folder is None:
        raise PreparationError("replace_source_item_anchors require the paper folder")
    if not isinstance(raw_replacements, Mapping):
        raise PreparationError("replace_source_item_anchors must be an object")
    for raw_key, raw_location in raw_replacements.items():
        key = str(raw_key).strip()
        location = str(raw_location or "").strip()
        if not key or key not in items or not location:
            raise PreparationError(
                "each replace_source_item_anchors entry needs an existing item and source_location"
            )
        items[key]["source_location"] = location
        items[key]["source_anchor_evidence"] = _canonical_anchor_evidence(folder, location)
        # A reconciliation core describes the previous conservative source
        # presentation span.  Replacing that span deliberately makes the old
        # reconciliation inapplicable; a configuration that still needs one
        # supplies it again in the later reconciliation phase.
        items[key].pop("source_presentation_reconciliation", None)


def _replace_source_item_locations(
    items: Mapping[str, dict[str, Any]], config: Mapping[str, Any], *, folder: Path | None
) -> None:
    """Update raw source-inventory locations without changing review excerpts.

    A damaged text extraction can still provide the complete, byte-pinned
    named-result inventory while an authenticated visual transcription supplies
    the legible source-to-Spec excerpt.  In that case source coverage changes
    location, not the selected semantic anchor.
    """

    raw_replacements = config.get("replace_source_item_locations", {})
    if raw_replacements in ({}, None):
        return
    if folder is None:
        raise PreparationError("replace_source_item_locations require the paper folder")
    if not isinstance(raw_replacements, Mapping):
        raise PreparationError("replace_source_item_locations must be an object")
    for raw_key, raw_location in raw_replacements.items():
        key = str(raw_key).strip()
        location = str(raw_location or "").strip()
        if not key or key not in items or not location:
            raise PreparationError(
                "each replace_source_item_locations entry needs an existing item and source_location"
            )
        _canonical_anchor_evidence(folder, location)
        items[key]["source_location"] = location
        # A reconciliation core describes the previous source presentation
        # span.  The later reconciliation phase can install a new one when
        # the replacement still needs a narrower core.
        items[key].pop("source_presentation_reconciliation", None)


def _replace_source_item_semantic_anchors(
    items: Mapping[str, dict[str, Any]], config: Mapping[str, Any], *, folder: Path | None
) -> None:
    """Select source-to-Spec excerpts without changing raw source coverage.

    This is separate from ``replace_source_item_anchors``.  The latter changes
    both historical roles for ordinary same-text sources; this operation keeps
    the source-inventory location and changes only the exact semantic-review
    excerpt.
    """

    raw_replacements = config.get("replace_source_item_semantic_anchors", {})
    if raw_replacements in ({}, None):
        return
    if folder is None:
        raise PreparationError(
            "replace_source_item_semantic_anchors require the paper folder"
        )
    if not isinstance(raw_replacements, Mapping):
        raise PreparationError("replace_source_item_semantic_anchors must be an object")
    for raw_key, raw_location in raw_replacements.items():
        key = str(raw_key).strip()
        location = str(raw_location or "").strip()
        if not key or key not in items or not location:
            raise PreparationError(
                "each replace_source_item_semantic_anchors entry needs an existing item and source_location"
            )
        items[key]["source_anchor_evidence"] = _canonical_anchor_evidence(
            folder, location
        )


def _apply_semantic_source_anchor_overrides(
    items: Mapping[str, dict[str, Any]], config: Mapping[str, Any], *, folder: Path | None
) -> None:
    """Pin a completed statement core without shrinking source coverage.

    The source inventory owns a conservative presentation span, including
    nearby explanation when extraction cannot determine a terminal reliably.
    A semantic reviewer should see the exact displayed statement instead of
    that incidental prose.  The override therefore adds a second, contained
    anchor solely for source-to-Lean comparison; it never changes the
    coverage anchor or source location.
    """

    raw_overrides = config.get("semantic_source_anchor_overrides", {})
    if raw_overrides in ({}, None):
        return
    if folder is None:
        raise PreparationError(
            "semantic_source_anchor_overrides require the paper folder"
        )
    if not isinstance(raw_overrides, Mapping):
        raise PreparationError("semantic_source_anchor_overrides must be an object")
    for raw_key, raw_plan in raw_overrides.items():
        key = str(raw_key).strip()
        if not key or key not in items or not isinstance(raw_plan, Mapping):
            raise PreparationError(
                "each semantic_source_anchor_overrides entry needs an existing item and object"
            )
        location = str(raw_plan.get("source_location") or "").strip()
        reason = str(raw_plan.get("reason") or "").strip()
        semantic_anchors = _canonical_anchor_evidence(folder, location) if location else []
        coverage_anchors = items[key].get("source_anchor_evidence")
        if (
            len(semantic_anchors) != 1
            or not isinstance(coverage_anchors, list)
            or not coverage_anchors
            or not reason
        ):
            raise PreparationError(
                f"{key}: semantic_source_anchor_overrides needs one exact contained "
                "source_location and a reason"
            )
        semantic = semantic_anchors[0]
        contained = any(
            isinstance(coverage, Mapping)
            and coverage.get("path") == semantic.get("path")
            and isinstance(coverage.get("line_start"), int)
            and isinstance(coverage.get("line_end"), int)
            and coverage["line_start"] <= semantic["line_start"]
            and semantic["line_end"] <= coverage["line_end"]
            for coverage in coverage_anchors
        )
        if not contained:
            raise PreparationError(
                f"{key}: semantic source anchor must be contained in an existing "
                "full source-coverage anchor"
            )
        items[key]["semantic_source_anchor_evidence"] = semantic_anchors
        items[key]["semantic_source_anchor_reason"] = reason


def _apply_semantic_context_requirements(
    items: Mapping[str, dict[str, Any]], config: Mapping[str, Any], *, folder: Path | None
) -> None:
    """Attach exact interpretation context without changing source-item identity.

    A theorem or definition may depend on a model convention stated elsewhere
    in the paper. That verbatim context belongs in semantic review input, but
    it is not another presentation of the item and must not be merged into the
    item's own source locator or anchor bundle. Keeping the two roles separate
    preserves intake-freeze identities while still making every premise
    available to the source-to-Lean reviewer.
    """

    raw_requirements = config.get("semantic_context_requirements", {})
    if raw_requirements in ({}, None):
        return
    if folder is None:
        raise PreparationError("semantic_context_requirements require the paper folder")
    if not isinstance(raw_requirements, Mapping):
        raise PreparationError("semantic_context_requirements must be an object")
    raw_replacements = config.get("replace_semantic_context_requirements_for", [])
    if raw_replacements is None:
        raw_replacements = []
    if (
        not isinstance(raw_replacements, list)
        or any(not isinstance(value, str) or not value.strip() for value in raw_replacements)
        or len({value.strip() for value in raw_replacements}) != len(raw_replacements)
    ):
        raise PreparationError(
            "replace_semantic_context_requirements_for must be a list of unique nonempty item keys"
        )
    replacement_keys = {value.strip() for value in raw_replacements}
    unknown_replacements = sorted(replacement_keys - {str(key) for key in items})
    if unknown_replacements:
        raise PreparationError(
            "replace_semantic_context_requirements_for names unknown item(s): "
            + ", ".join(unknown_replacements)
        )
    allowed_roles = {
        "definition",
        "model",
        "model_construction",
        "scope",
        "prior_result",
        "stated_antecedent",
    }
    for raw_key, raw_contexts in raw_requirements.items():
        key = str(raw_key).strip()
        if not key or key not in items or not isinstance(raw_contexts, list) or not raw_contexts:
            raise PreparationError(
                "each semantic_context_requirements entry needs an existing item and nonempty list"
            )
        contexts: list[dict[str, Any]] = []
        for index, raw_context in enumerate(raw_contexts):
            if not isinstance(raw_context, Mapping):
                raise PreparationError(
                    f"{key}: semantic_context_requirements[{index}] must be an object"
                )
            semantic_role = str(raw_context.get("semantic_role") or "").strip()
            source_location = str(raw_context.get("source_location") or "").strip()
            if semantic_role not in allowed_roles or not source_location:
                raise PreparationError(
                    f"{key}: semantic context needs a bounded semantic_role and source_location"
                )
            contexts.append(
                {
                    "semantic_role": semantic_role,
                    "source_anchor_evidence": _canonical_anchor_evidence(
                        folder, source_location
                    ),
                    **(
                        {
                            "cited_source_artifact_id": str(
                                raw_context.get("cited_source_artifact_id") or ""
                            ).strip()
                        }
                        if raw_context.get("cited_source_artifact_id") is not None
                        else {}
                    ),
                }
            )
        existing_contexts = (
            []
            if key in replacement_keys
            else items[key].get("semantic_context_requirements", [])
        )
        if existing_contexts is None:
            existing_contexts = []
        if not isinstance(existing_contexts, list):
            raise PreparationError(
                f"{key}: existing semantic_context_requirements must be a list"
            )
        items[key]["semantic_context_requirements"] = _deduplicated_values(
            [*existing_contexts, *contexts]
        )


def _apply_source_core_projections(
    items: Mapping[str, dict[str, Any]], config: Mapping[str, Any]
) -> None:
    """Bind an explicitly selected literal source core to its current typed route."""

    raw_projections = config.get("source_core_projections", {})
    if raw_projections in ({}, None):
        return
    if not isinstance(raw_projections, Mapping):
        raise PreparationError("source_core_projections must be an object")
    for raw_key, raw_description in raw_projections.items():
        key = str(raw_key).strip()
        description = str(raw_description).strip()
        item = items.get(key)
        contract = item.get("semantic_contract") if item is not None else None
        if not key or item is None or not description or not isinstance(contract, Mapping):
            raise PreparationError(
                "each source_core_projections entry needs a selected source item "
                "and nonempty description"
            )
        spec = str(contract.get("spec_declaration") or "").strip()
        endpoint = str(contract.get("evidence_declaration") or "").strip()
        if not spec or not endpoint:
            raise PreparationError(
                f"{key}: source-core projection requires a complete semantic contract"
            )
        item["source_core_projection"] = {
            "classification": "literal_source_core",
            "description": description,
            "direct_declaration": endpoint,
            "spec_declaration": spec,
        }


def _apply_source_presentation_reconciliations(
    items: Mapping[str, dict[str, Any]],
    config: Mapping[str, Any],
    *,
    folder: Path | None,
) -> None:
    """Record a reviewed statement core inside a conservative text span.

    The source-only named-result index may intentionally retain explanation or
    a neighboring summary after a complete visible definition/theorem.  This
    configuration binds the already-existing source item to one exact
    byte-pinned statement core without changing its semantic source bundle or
    inventing a Lean route.
    """

    raw_reconciliations = config.get("source_presentation_reconciliations", {})
    if raw_reconciliations in ({}, None):
        return
    if folder is None:
        raise PreparationError(
            "source_presentation_reconciliations require the paper folder"
        )
    if not isinstance(raw_reconciliations, Mapping):
        raise PreparationError(
            "source_presentation_reconciliations must be an object"
        )
    for raw_name, raw_plan in raw_reconciliations.items():
        name = str(raw_name).strip()
        if not name or name not in items or not isinstance(raw_plan, Mapping):
            raise PreparationError(
                "each source_presentation_reconciliations entry needs an existing item and object"
            )
        presentation_kind = str(
            raw_plan.get("presentation_kind") or ""
        ).strip()
        presentation_label = str(
            raw_plan.get("presentation_label") or ""
        ).strip()
        core_locator = str(raw_plan.get("core_anchor_locator") or "").strip()
        boundary_reason = str(raw_plan.get("boundary_reason") or "").strip()
        semantic_basis = str(raw_plan.get("semantic_basis") or "").strip()
        validator = str(raw_plan.get("validator") or "").strip()
        validated_at = str(raw_plan.get("validated_at") or "").strip()
        core_anchors = (
            _canonical_anchor_evidence(folder, core_locator)
            if core_locator
            else []
        )
        if (
            not presentation_kind
            or not presentation_label
            or len(core_anchors) != 1
            or boundary_reason
            not in SOURCE_PRESENTATION_RECONCILIATION_BOUNDARY_REASONS
            or not semantic_basis
            or not validator
            or not validated_at
        ):
            raise PreparationError(
                f"{name}: source_presentation_reconciliations needs source kind/label, "
                "one core anchor, supported boundary reason, basis, validator, "
                "and timestamp"
            )
        items[name]["source_presentation_reconciliation"] = {
            "schema": 1,
            "relation": "conservative_text_span_core",
            "presentation_kind": presentation_kind,
            "presentation_label": presentation_label,
            "core_anchor": core_anchors[0],
            "boundary_reason": boundary_reason,
            "semantic_basis": semantic_basis,
            "validator": validator,
            "validated_at": validated_at,
        }


def _apply_prose_definition_reconciliations(
    items: dict[str, dict[str, Any]],
    config: Mapping[str, Any],
    *,
    presentation_sha256_by_id: Mapping[str, str] | None = None,
) -> None:
    """Persist reviewed literal-definition bindings across preparation reruns."""

    raw_reconciliations = config.get("prose_definition_reconciliations", {})
    if not isinstance(raw_reconciliations, Mapping):
        raise PreparationError("prose_definition_reconciliations must be an object")
    for raw_name, raw_reconciliation in raw_reconciliations.items():
        name = str(raw_name).strip()
        if not name or name not in items or not isinstance(raw_reconciliation, Mapping):
            raise PreparationError(
                "each prose_definition_reconciliations entry needs an existing item and object"
            )
        item = items[name]
        if str(item.get("source_kind") or "").strip().lower() != "definition":
            raise PreparationError(
                f"{name}: prose_definition_reconciliations applies only to definitions"
            )
        presentation_sha = str(raw_reconciliation.get("presentation_sha256") or "").strip()
        presentation_id = str(raw_reconciliation.get("presentation_id") or "").strip()
        if presentation_id:
            if presentation_sha:
                raise PreparationError(
                    f"{name}: prose_definition_reconciliations must use either "
                    "presentation_id or presentation_sha256, not both"
                )
            presentation_sha = str(
                (presentation_sha256_by_id or {}).get(presentation_id) or ""
            ).strip()
        semantic_basis = str(raw_reconciliation.get("semantic_basis") or "").strip()
        validator = str(raw_reconciliation.get("validator") or "").strip()
        validator_type = str(raw_reconciliation.get("validator_type") or "").strip()
        validated_at = str(raw_reconciliation.get("validated_at") or "").strip()
        if (
            not re.fullmatch(r"[0-9a-fA-F]{64}", presentation_sha)
            or len(semantic_basis) < 20
            or not validator
            or validator_type not in {"agent", "human", "model"}
            or not validated_at
        ):
            raise PreparationError(
                f"{name}: prose_definition_reconciliations needs a presentation SHA-256, "
                "or a current reviewed presentation_id, plus substantive basis, "
                "validator, validator type, and timestamp"
            )
        statement = str(item.get("statement") or "").strip()
        if not statement:
            raise PreparationError(
                f"{name}: prose_definition_reconciliations needs a source-map statement"
            )
        statement_digest = hashlib.sha256(
            " ".join(statement.replace("\r\n", "\n").replace("\r", "\n").split()).encode(
                "utf-8"
            )
        ).hexdigest()
        item["source_prose_definition_reconciliation"] = {
            "schema": 2,
            "relation": "source_item_represents_prose_definition",
            "presentation_sha256": presentation_sha.lower(),
            "source_item_statement_sha256": statement_digest,
            "judgment": "semantically_equivalent",
            "semantic_basis": semantic_basis,
            "validator": validator,
            "validator_type": validator_type,
            "validated_at": validated_at,
        }


def prepare(
    source_map: dict[str, Any], config: Mapping[str, Any], *, folder: Path | None = None
) -> dict[str, Any]:
    paper = str(config.get("paper") or "").strip()
    if paper != str(source_map.get("paper") or "").strip():
        raise PreparationError("config paper must match paper_statement_map.json")
    namespace = str(config.get("namespace") or "").strip()
    if not namespace:
        raise PreparationError("config needs namespace")
    interface_module = str(config.get("paper_interface_module", "PaperInterface")).strip()
    if "." in interface_module:
        raise PreparationError(
            "paper_interface_module must be one direct namespace component or empty"
        )
    semantic_preflight_import_module = str(
        config.get("semantic_preflight_import_module") or ""
    ).strip()
    specs = as_string_list(config.get("include_specs"), label="include_specs")
    policy_provided = CLOSEOUT_REVIEW_POLICY_FIELD in config
    raw_closeout_review_policy = config.get(CLOSEOUT_REVIEW_POLICY_FIELD)
    try:
        existing_closeout_review_policy = (
            explicit_closeout_review_policy_from_source_map(source_map)
        )
        closeout_review_policy = (
            resolve_closeout_review_policy(raw_closeout_review_policy)
            if policy_provided
            else existing_closeout_review_policy
        )
    except FormalizationProtocolError as error:
        raise PreparationError(str(error)) from error
    existing_inventory_review = source_map.get(
        "source_named_result_inventory_review"
    )
    if (
        existing_closeout_review_policy is not None
        and closeout_review_policy is not None
        and closeout_review_policy_material_projection(
            existing_closeout_review_policy
        )
        != closeout_review_policy_material_projection(closeout_review_policy)
        and isinstance(existing_inventory_review, Mapping)
        and existing_inventory_review.get("complete") is True
    ):
        raise PreparationError(
            "a completed source inventory has already fixed the source/repeat "
            "scope and scope approval in closeout_review_policy"
        )
    semantic_route_schema = config.get("semantic_route_schema")
    if semantic_route_schema not in {None, 2}:
        raise PreparationError("semantic_route_schema must be 2 when provided")
    raw_semantic_declarations = config.get("source_semantic_declarations", {})
    if not isinstance(raw_semantic_declarations, Mapping) or not all(
        isinstance(key, str)
        and key.strip()
        and isinstance(value, list)
        and bool(value)
        and all(isinstance(name, str) and name.strip() for name in value)
        for key, value in raw_semantic_declarations.items()
    ):
        raise PreparationError(
            "source_semantic_declarations must map source-item ids to nonempty Lean declaration lists"
        )
    source_semantic_declarations = {
        str(key).strip(): [str(name).strip() for name in value]
        for key, value in raw_semantic_declarations.items()
    }
    if source_semantic_declarations and semantic_route_schema != 2:
        raise PreparationError(
            "source_semantic_declarations require semantic_route_schema 2"
        )
    raw_prerequisite_sources = config.get(
        "paper_semantic_prerequisite_sources", {}
    )
    if not isinstance(raw_prerequisite_sources, Mapping) or not all(
        isinstance(declaration, str)
        and declaration.strip()
        and isinstance(source_item, str)
        and source_item.strip()
        for declaration, source_item in raw_prerequisite_sources.items()
    ):
        raise PreparationError(
            "paper_semantic_prerequisite_sources must map nonempty Lean "
            "declaration names to nonempty source-item ids"
        )
    paper_semantic_prerequisite_sources = {
        str(declaration).strip(): str(source_item).strip()
        for declaration, source_item in raw_prerequisite_sources.items()
    }
    if paper_semantic_prerequisite_sources and semantic_route_schema != 2:
        raise PreparationError(
            "paper_semantic_prerequisite_sources require semantic_route_schema 2"
        )
    raw_library_prerequisite_sources = config.get(
        "library_semantic_prerequisite_sources", {}
    )
    if not isinstance(raw_library_prerequisite_sources, Mapping) or not all(
        isinstance(declaration, str)
        and declaration.strip()
        and isinstance(source_item, str)
        and source_item.strip()
        for declaration, source_item in raw_library_prerequisite_sources.items()
    ):
        raise PreparationError(
            "library_semantic_prerequisite_sources must map nonempty Lean "
            "declaration names to nonempty source-item ids"
        )
    library_semantic_prerequisite_sources = {
        str(declaration).strip(): str(source_item).strip()
        for declaration, source_item in raw_library_prerequisite_sources.items()
    }
    if library_semantic_prerequisite_sources and semantic_route_schema != 2:
        raise PreparationError(
            "library_semantic_prerequisite_sources require semantic_route_schema 2"
        )
    cited_registry_schema = config.get("cited_source_artifacts_schema")
    raw_cited_registry = config.get("cited_source_artifacts")
    source_map_has_cited_registry = (
        source_map.get("cited_source_artifacts_schema") is not None
        or source_map.get("cited_source_artifacts") is not None
    )
    if cited_registry_schema is None and raw_cited_registry is None:
        if source_map_has_cited_registry:
            raise PreparationError(
                "a source map with cited_source_artifacts requires the preparation "
                "config to own that registry"
            )
        cited_registry: list[dict[str, Any]] | None = None
    else:
        if (
            not isinstance(cited_registry_schema, int)
            or isinstance(cited_registry_schema, bool)
            or cited_registry_schema != 1
        ):
            raise PreparationError("cited_source_artifacts_schema must be 1")
        if (
            not isinstance(raw_cited_registry, list)
            or not raw_cited_registry
            or any(not isinstance(value, Mapping) for value in raw_cited_registry)
        ):
            raise PreparationError("cited_source_artifacts must be a nonempty object list")
        cited_registry = [dict(value) for value in raw_cited_registry]
    raw_items = source_map.get("items")
    if not isinstance(raw_items, Mapping):
        raise PreparationError("paper_statement_map.json has no items object")
    items = {str(key): dict(value) for key, value in raw_items.items() if isinstance(value, Mapping)}
    if len(items) != len(raw_items):
        raise PreparationError("every existing source-map item must be an object")
    _add_source_items(items, config, folder=folder)
    _replace_source_item_locations(items, config, folder=folder)
    _replace_source_item_anchors(items, config, folder=folder)
    _replace_source_item_semantic_anchors(items, config, folder=folder)
    _apply_semantic_source_anchor_overrides(items, config, folder=folder)
    _reclassify_source_item_kinds(items, config)
    _apply_source_presentation_reconciliations(items, config, folder=folder)
    inventory_review_plan = config.get("source_named_result_inventory_review")
    prose_presentations: list[dict[str, Any]] | None = None
    prose_sha256_by_id: dict[str, str] = {}
    if inventory_review_plan is not None:
        if folder is None or not isinstance(inventory_review_plan, Mapping):
            raise PreparationError(
                "source_named_result_inventory_review requires a paper folder and object"
            )
        try:
            prose_presentations, prose_sha256_by_id = (
                materialize_prose_definition_presentations(
                    folder,
                    inventory_review_plan.get("prose_definition_presentations"),
                )
            )
        except SourceInventoryReviewError as error:
            raise PreparationError(str(error)) from error
    if closeout_review_policy is not None:
        existing_review = source_map.get("source_named_result_inventory_review")
        existing_partition = (
            existing_review.get("source_region_partition")
            if isinstance(existing_review, Mapping)
            else None
        )
        if (
            not isinstance(inventory_review_plan, Mapping)
            or inventory_review_plan.get("source_region_partition") is None
        ) and existing_partition is None:
            raise PreparationError(
                "closeout_review_policy requires one complete source_region_partition"
            )
    _atomize_source_items(items, config)
    _consolidate_source_items(items, config, folder=folder)
    _consolidate_presentation_aliases(items, config, folder=folder)
    _apply_prose_definition_reconciliations(
        items,
        config,
        presentation_sha256_by_id=prose_sha256_by_id,
    )
    _retire_non_source_items(items, config)

    overrides_raw = config.get("source_item_for_spec", {})
    if not isinstance(overrides_raw, Mapping) or not all(
        isinstance(key, str) and isinstance(value, str)
        for key, value in overrides_raw.items()
    ):
        raise PreparationError("source_item_for_spec must be a string-to-string object")
    overrides = {str(key).strip(): str(value).strip() for key, value in overrides_raw.items()}
    unknown_overrides = sorted(set(overrides) - set(specs))
    if unknown_overrides:
        raise PreparationError(
            "source_item_for_spec names not selected by include_specs: "
            + ", ".join(unknown_overrides)
        )

    raw_evidence_names = config.get("evidence_declaration_for_spec", {})
    if not isinstance(raw_evidence_names, Mapping) or not all(
        isinstance(key, str) and isinstance(value, str) and value.strip()
        for key, value in raw_evidence_names.items()
    ):
        raise PreparationError(
            "evidence_declaration_for_spec must be a string-to-nonempty-string object"
        )
    evidence_names = {
        str(key).strip(): str(value).strip()
        for key, value in raw_evidence_names.items()
    }
    unknown_evidence_names = sorted(set(evidence_names) - set(specs))
    if unknown_evidence_names:
        raise PreparationError(
            "evidence_declaration_for_spec names not selected by include_specs: "
            + ", ".join(unknown_evidence_names)
        )

    raw_evidence_modes = config.get("evidence_mode_for_spec", {})
    if not isinstance(raw_evidence_modes, Mapping) or not all(
        isinstance(key, str) and isinstance(value, str) and value.strip()
        for key, value in raw_evidence_modes.items()
    ):
        raise PreparationError("evidence_mode_for_spec must be a string-to-nonempty-string object")
    evidence_modes = {
        str(key).strip(): str(value).strip()
        for key, value in raw_evidence_modes.items()
    }
    unknown_evidence_modes = sorted(set(evidence_modes) - set(specs))
    if unknown_evidence_modes:
        raise PreparationError(
            "evidence_mode_for_spec names not selected by include_specs: "
            + ", ".join(unknown_evidence_modes)
        )
    invalid_evidence_modes = sorted(
        spec for spec, mode in evidence_modes.items()
        if mode not in {"proves", "refutes", "definitionally_realizes"}
    )
    if invalid_evidence_modes:
        raise PreparationError(
            "evidence_mode_for_spec values must be `proves`, `refutes`, or `definitionally_realizes`: "
            + ", ".join(invalid_evidence_modes)
        )

    raw_review_target_kinds = config.get("semantic_review_target_kind_for_spec", {})
    if not isinstance(raw_review_target_kinds, Mapping) or not all(
        isinstance(key, str) and isinstance(value, str) and value.strip()
        for key, value in raw_review_target_kinds.items()
    ):
        raise PreparationError(
            "semantic_review_target_kind_for_spec must be a string-to-nonempty-string object"
        )
    review_target_kinds = {
        str(key).strip(): str(value).strip()
        for key, value in raw_review_target_kinds.items()
    }
    unknown_review_target_kinds = sorted(set(review_target_kinds) - set(specs))
    if unknown_review_target_kinds:
        raise PreparationError(
            "semantic_review_target_kind_for_spec names not selected by include_specs: "
            + ", ".join(unknown_review_target_kinds)
        )
    if review_target_kinds:
        raise PreparationError(
            "semantic_review_target_kind_for_spec is retired: every selected "
            "source claim must be reviewed through its paired transparent `...Spec : Prop`, "
            "including definitions with a definitionally-realizes proof endpoint"
        )

    merge_raw = config.get("merge_source_items", {})
    if not isinstance(merge_raw, Mapping) or not all(
        isinstance(key, str) and isinstance(value, list)
        and all(isinstance(item, str) for item in value)
        for key, value in merge_raw.items()
    ):
        raise PreparationError("merge_source_items must map a source item to a string list")
    for raw_canonical, raw_aliases in merge_raw.items():
        canonical = str(raw_canonical).strip()
        aliases = [str(item).strip() for item in raw_aliases]
        if canonical not in items:
            raise PreparationError(f"merge canonical source item `{canonical}` is absent")
        if not aliases or len(aliases) != len(set(aliases)):
            raise PreparationError(f"{canonical}: merged source items must be a nonempty unique list")
        canonical_item = items[canonical]
        canonical_anchors = list(canonical_item.get("source_anchor_evidence") or [])
        locations = [
            location.strip()
            for location in str(
                canonical_item.get("source_location") or ""
            ).split(";")
            if location.strip()
        ]
        merged_any = False
        for alias in aliases:
            if alias == canonical:
                raise PreparationError(f"{canonical}: cannot merge a source item into itself")
            if alias not in items:
                # A previous preparation may already have folded this exact
                # context presentation into its canonical raw bundle. The
                # command remains idempotent; current anchor hashes still
                # decide whether that bundled evidence is usable.
                continue
            alias_item = items.pop(alias)
            merged_any = True
            canonical_anchors.extend(alias_item.get("source_anchor_evidence") or [])
            locations.extend(
                location.strip()
                for location in str(
                    alias_item.get("source_location") or ""
                ).split(";")
                if location.strip()
            )
        # ``add_source_items`` deliberately leaves an already-materialized
        # canonical row alone, while re-materializing temporary context rows
        # that an earlier merge removed.  Therefore a second preparation sees
        # the canonical row's prior context anchors *and* the same fresh
        # context rows.  Preserve one exact copy of each anchor/location so a
        # deterministic rerun cannot change the source bundle digest and
        # spuriously invalidate semantic review evidence.
        canonical_item["source_anchor_evidence"] = _deduplicated_values(
            canonical_anchors
        )
        canonical_item["source_location"] = "; ".join(
            str(location)
            for location in _deduplicated_values(
                [location for location in locations if location]
            )
        )
        merge_note = (
            "The raw source bundle also includes the explicitly merged source presentation(s) "
            "needed to interpret this one canonical claim."
        )
        existing_note = str(canonical_item.get("source_note") or "").strip()
        if merged_any and merge_note not in existing_note:
            canonical_item["source_note"] = (existing_note + " " + merge_note).strip()

    _deduplicate_source_bundles(items)
    _apply_semantic_context_requirements(items, config, folder=folder)

    aliases_raw = config.get("presentation_aliases", {})
    if not isinstance(aliases_raw, Mapping):
        raise PreparationError("presentation_aliases must be an object")
    presentation_aliases: dict[str, dict[str, Any]] = {}
    for raw_alias, raw_value in aliases_raw.items():
        alias = str(raw_alias).strip()
        if not isinstance(raw_value, Mapping):
            raise PreparationError(f"presentation alias `{alias}` must be an object")
        canonical = str(raw_value.get("canonical_source_item") or "").strip()
        basis = str(raw_value.get("semantic_basis") or "").strip()
        if not alias or alias not in items or not canonical or canonical not in items or not basis:
            raise PreparationError(
                f"presentation alias `{alias}` needs an existing canonical source item and semantic_basis"
            )
        label_relation = str(
            raw_value.get(SOURCE_PRESENTATION_ALIAS_LABEL_RELATION_FIELD)
            or SOURCE_PRESENTATION_ALIAS_SAME_VISIBLE_LABEL
        ).strip()
        if label_relation not in {
            SOURCE_PRESENTATION_ALIAS_SAME_VISIBLE_LABEL,
            SOURCE_PRESENTATION_ALIAS_EXPLICIT_RENUMBERED_RESTATEMENT,
        }:
            raise PreparationError(
                f"presentation alias `{alias}` has an unsupported label_relation"
            )
        alias_plan: dict[str, Any] = {
            "canonical_source_item": canonical,
            "semantic_basis": basis,
        }
        if label_relation == SOURCE_PRESENTATION_ALIAS_EXPLICIT_RENUMBERED_RESTATEMENT:
            evidence_locator = str(
                raw_value.get("source_restatement_evidence_location") or ""
            ).strip()
            if not evidence_locator:
                raise PreparationError(
                    f"presentation alias `{alias}` needs source_restatement_evidence_location "
                    "for a renumbered restatement"
                )
            if folder is None:
                raise PreparationError(
                    "renumbered presentation aliases require the paper folder"
                )
            evidence = _canonical_anchor_evidence(folder, evidence_locator)
            if len(evidence) != 1:
                raise PreparationError(
                    f"presentation alias `{alias}` needs one exact restatement evidence anchor"
                )
            alias_plan[SOURCE_PRESENTATION_ALIAS_LABEL_RELATION_FIELD] = label_relation
            alias_plan[SOURCE_PRESENTATION_ALIAS_RENUMBERED_EVIDENCE_FIELD] = evidence[0]
        presentation_aliases[alias] = alias_plan

    source_items_for_spec: dict[str, str] = {}
    for spec in specs:
        configured = overrides.get(spec)
        if configured:
            if configured not in items:
                raise PreparationError(f"{spec}: configured source item `{configured}` is absent")
            source_items_for_spec[spec] = configured
            continue
        routes = [
            key
            for key, item in items.items()
            if spec in {
                declaration.rsplit(".", maxsplit=1)[-1]
                for declaration in item.get("lean_declarations", [])
                if isinstance(declaration, str)
            }
        ]
        if len(routes) != 1:
            rendered = ", ".join(routes) if routes else "none"
            raise PreparationError(
                f"{spec}: needs one explicit source_item_for_spec route; found {rendered}"
            )
        source_items_for_spec[spec] = routes[0]

    reused_items: dict[str, list[str]] = {}
    for spec, key in source_items_for_spec.items():
        reused_items.setdefault(key, []).append(spec)
    ambiguous_items = {key: values for key, values in reused_items.items() if len(values) > 1}
    if ambiguous_items:
        details = "; ".join(
            f"{key}: {', '.join(values)}" for key, values in sorted(ambiguous_items.items())
        )
        raise PreparationError(
            "one source-map item cannot silently represent multiple canonical Specs; "
            "atomize the source presentation first (" + details + ")"
        )

    selected_by_item = {key: spec for spec, key in source_items_for_spec.items()}
    unknown_semantic_declaration_items = sorted(
        set(source_semantic_declarations) - set(items)
    )
    if unknown_semantic_declaration_items:
        raise PreparationError(
            "source_semantic_declarations names absent source items: "
            + ", ".join(unknown_semantic_declaration_items)
        )
    unknown_prerequisite_source_items = sorted(
        set(paper_semantic_prerequisite_sources.values()) - set(items)
    )
    if unknown_prerequisite_source_items:
        raise PreparationError(
            "paper_semantic_prerequisite_sources names absent source items: "
            + ", ".join(unknown_prerequisite_source_items)
        )
    unknown_library_prerequisite_source_items = sorted(
        set(library_semantic_prerequisite_sources.values()) - set(items)
    )
    if unknown_library_prerequisite_source_items:
        raise PreparationError(
            "library_semantic_prerequisite_sources names absent source items: "
            + ", ".join(unknown_library_prerequisite_source_items)
        )
    overlap_semantic_roles = sorted(
        set(source_semantic_declarations) & set(selected_by_item)
    )
    if overlap_semantic_roles:
        raise PreparationError(
            "one source item cannot be both a result contract and a source semantic declaration: "
            + ", ".join(overlap_semantic_roles)
        )
    if semantic_route_schema == 2:
        invalid_result_items = sorted(
            key
            for key in selected_by_item
            if str(items[key].get("source_kind") or "").strip().lower()
            not in PROOF_CONTRACT_SOURCE_KINDS
        )
        invalid_semantic_items = sorted(
            key
            for key in source_semantic_declarations
            if str(items[key].get("source_kind") or "").strip().lower()
            not in SOURCE_SEMANTIC_DECLARATION_KINDS
        )
        if invalid_result_items:
            raise PreparationError(
                "role schema 2 reserves include_specs for explicitly selected "
                "proof-bearing source presentations: "
                + ", ".join(invalid_result_items)
            )
        if invalid_semantic_items:
            raise PreparationError(
                "role schema 2 source semantic declarations have incompatible source kinds: "
                + ", ".join(invalid_semantic_items)
            )
        missing_evidence_names = sorted(set(specs) - set(evidence_names))
        if missing_evidence_names:
            raise PreparationError(
                "role schema 2 requires an explicit evidence_declaration_for_spec "
                "for every selected result: " + ", ".join(missing_evidence_names)
            )
    existing_evidence_names: dict[str, str] = {}
    for spec, key in source_items_for_spec.items():
        contract = items[key].get("semantic_contract")
        if not isinstance(contract, Mapping):
            continue
        endpoint = str(contract.get("evidence_declaration") or "").strip()
        if endpoint:
            # A source map which already pairs this exact transparent Spec
            # with its checked endpoint should keep that endpoint when a
            # mechanical preparation only activates/rebuilds the v11 surface.
            # An explicit configuration remains authoritative.
            existing_evidence_names[spec] = endpoint.rsplit(".", maxsplit=1)[-1]
    raw_dispositions = config.get("unselected_item_dispositions", {})
    if not isinstance(raw_dispositions, Mapping):
        raise PreparationError("unselected_item_dispositions must be an object")
    unselected_dispositions: dict[str, dict[str, Any]] = {}
    for raw_key, raw_value in raw_dispositions.items():
        key = str(raw_key).strip()
        if not key or key not in items or not isinstance(raw_value, Mapping):
            raise PreparationError(
                "each unselected_item_dispositions entry needs an existing source-map item and object"
            )
        role = str(raw_value.get("inventory_role") or "").strip()
        disposition = str(raw_value.get("scope_disposition") or "").strip()
        reason = str(raw_value.get("reason") or "").strip()
        source_status = str(raw_value.get("source_status") or "").strip()
        subsumed_by_source_item = str(
            raw_value.get("subsumed_by_source_item") or ""
        ).strip()
        if not role or not disposition or not reason:
            raise PreparationError(
                f"{key}: unselected disposition needs inventory_role, scope_disposition, and reason"
            )
        support_declarations = as_string_list(
            raw_value.get("support_lean_declarations", []),
            label=f"{key}.support_lean_declarations",
        )
        defect_ids = as_string_list(
            raw_value.get("source_defect_ids", []),
            label=f"{key}.source_defect_ids",
        )
        if len(set(defect_ids)) != len(defect_ids):
            raise PreparationError(f"{key}.source_defect_ids must be unique")
        if support_declarations and role != "quarantined_source_defect":
            raise PreparationError(
                f"{key}: support_lean_declarations are reserved for a quarantined_source_defect disposition"
            )
        if defect_ids and role != "quarantined_source_defect":
            raise PreparationError(
                f"{key}: source_defect_ids are reserved for a quarantined_source_defect disposition"
            )
        if subsumed_by_source_item:
            if role != "subsumed_by_selected_result":
                raise PreparationError(
                    f"{key}: subsumed_by_source_item requires the "
                    "subsumed_by_selected_result inventory role"
                )
            if source_status != "subsumed_by_selected_result":
                raise PreparationError(
                    f"{key}: a subsumed source claim must use source_status "
                    "subsumed_by_selected_result"
                )
            if subsumed_by_source_item not in selected_by_item:
                raise PreparationError(
                    f"{key}: subsumed_by_source_item must name a selected source item"
                )
        elif role == "subsumed_by_selected_result":
            raise PreparationError(
                f"{key}: subsumed_by_selected_result needs subsumed_by_source_item"
            )
        if key in selected_by_item:
            raise PreparationError(
                f"{key}: selected source item cannot also receive an unselected disposition"
            )
        unselected_dispositions[key] = {
            "inventory_role": role,
            "scope_disposition": disposition,
            "reason": reason,
            "source_status": source_status,
            "source_status_configured": "source_status" in raw_value,
            "subsumed_by_source_item": subsumed_by_source_item,
            "support_lean_declarations": support_declarations,
            "source_defect_ids": defect_ids,
            "source_defect_ids_configured": "source_defect_ids" in raw_value,
        }

    # Materialize selected-result dispositions before pinning approved
    # corrections. Corrections below then replace this provisional status by
    # their stronger reviewed target record, while finite replacements remain
    # visible directly on the generated source-map row.
    _apply_selected_item_dispositions(items, config, selected_by_item)

    # Pin approved corrected targets before assigning typed routes.  A
    # corrected theorem is then routed through its selected Spec, while a
    # corrected definition or algorithm retains its direct semantic-
    # declaration route.  Applying corrections after this loop would overwrite
    # the latter role with the descriptive `corrected_source_target` marker and
    # leave a genuine claim-bearing source item without a typed route.
    _apply_corrected_targets(items, config, folder=folder)
    _upgrade_legacy_corrected_target_approval_artifacts(
        items, config, folder=folder
    )
    _apply_legacy_semantic_context_roles(items, config)

    for key, item in items.items():
        selected = selected_by_item.get(key)
        semantic_roots = source_semantic_declarations.get(key)
        if (selected is not None or semantic_roots is not None) and str(item.get("source_status") or "").strip().lower() in {"support_only", "formalization_pending"}:
            # A direct route supersedes this old support/pending classification;
            # selecting it does not itself issue a positive semantic verdict.
            item.pop("source_status")
        if semantic_roots is not None:
            item.pop("semantic_contract", None)
            # ``semantic_surface`` is an old parser-shaped presentation lint.
            # Schema-2 direct routes are reviewed through Lean's bounded
            # transparent target and graph-owned prerequisite surface.  Keeping
            # an earlier token contract after replacing a source
            # definition/model target can describe the retired display rather
            # than the current semantic declaration.
            item.pop("semantic_surface", None)
            item.pop("semantic_surface_origin", None)
            # A source-model or proof-side condition can be semantically
            # material to a selected result without being a separate
            # source-facing paper claim.  Preserve that explicit distinction:
            # it remains in the Lean-owned semantic graph, but does not become
            # a synthetic ordinary-review row merely because it has a direct
            # declaration route.
            item["claim_bearing"] = (
                str(item.get("source_kind") or "").strip().lower()
                in {"definition", "predicate_vocabulary"}
                or item.get("claim_bearing") is not False
            )
            item["inventory_role"] = "source_semantic_declaration"
            # A typed semantic route replaces any earlier migration-time
            # disposition.  Retaining a stale pending/exclusion disposition
            # would make the same source item simultaneously current and
            # unresolved in downstream closeout gates.
            item.pop("scope_disposition", None)
            item.pop("scope_disposition_note", None)
            # A direct route also supersedes a former user-approved scope
            # exclusion.  Leaving its legacy coverage label or approval
            # record behind makes a current source declaration appear both
            # reviewed and excluded in downstream presentation/audit output.
            if item.get("coverage_status") == "user_approved_scope_exclusion":
                item.pop("coverage_status", None)
            item.pop("user_approved_scope_exclusion", None)
            item["lean_declarations"] = semantic_roots
            item.pop("source_presentation_alias", None)
            item.pop("support_lean_declarations", None)
            item.pop("proof_lean_declarations", None)
            item.pop("source_spec_correspondence", None)
            atoms = item.get("source_claim_atoms")
            if isinstance(atoms, list):
                for atom in atoms:
                    if isinstance(atom, dict):
                        atom["reviewed_lean_route"] = semantic_roots[0]
            continue
        if key in presentation_aliases:
            item.pop("semantic_contract", None)
            alias = presentation_aliases[key]
            item["source_presentation_alias"] = {
                "schema": 1,
                "canonical_source_item": alias["canonical_source_item"],
                "relation": "repeated_source_presentation",
                "semantic_basis": alias["semantic_basis"],
                "validator": "v11 source-first review-surface preparation",
                "validated_at": "2026-08-18T00:00:00Z",
            }
            if (
                alias.get(SOURCE_PRESENTATION_ALIAS_LABEL_RELATION_FIELD)
                == SOURCE_PRESENTATION_ALIAS_EXPLICIT_RENUMBERED_RESTATEMENT
            ):
                item["source_presentation_alias"][
                    SOURCE_PRESENTATION_ALIAS_LABEL_RELATION_FIELD
                ] = SOURCE_PRESENTATION_ALIAS_EXPLICIT_RENUMBERED_RESTATEMENT
                item["source_presentation_alias"][
                    SOURCE_PRESENTATION_ALIAS_RENUMBERED_EVIDENCE_FIELD
                ] = alias[SOURCE_PRESENTATION_ALIAS_RENUMBERED_EVIDENCE_FIELD]
            # A repeated source presentation remains claim-bearing, but its
            # canonical source item alone owns the source-to-Spec route.
            # Retained old direct routes would turn the alias into a hidden
            # second semantic claim.
            item.pop("lean_declarations", None)
            item.pop("proof_lean_declarations", None)
            item.pop("support_lean_declarations", None)
            item.pop("source_spec_correspondence", None)
        else:
            item.pop("source_presentation_alias", None)
        if selected is None:
            item.pop("semantic_contract", None)
            # The source inventory stays intact. A later audit must either add
            # a semantic target or give this genuine source claim an explicit,
            # source-grounded disposition; it cannot disappear during a
            # mechanical interface migration.
            if key in presentation_aliases:
                # A repeated byte-pinned presentation is retained for source
                # traceability but is not a second paper claim or denominator
                # row.  Keep it explicitly non-claim-bearing so the strict
                # v11 source/spec gate cannot create a duplicate obligation.
                item["claim_bearing"] = False
                item["inventory_role"] = "source_presentation_alias"
                continue
            if (
                str(item.get("source_status") or "").strip().lower() == "support_only"
                and key not in unselected_dispositions
            ):
                # A named intermediate source lemma remains visible to the
                # source inventory, but its explicit support-only disposition
                # says that it is proof support for a retained result rather
                # than an additional direct source-to-Spec obligation.
                item["claim_bearing"] = item.get("claim_bearing") is True or (
                    source_item_is_named_theoretical_statement(item)
                )
                item["inventory_role"] = "proof_support"
                continue
            configured = unselected_dispositions.get(key)
            if configured is not None:
                # An unselected disposition records why a source presentation
                # has no current v11 Spec route.  It cannot turn a real source
                # claim into non-claim inventory: normal-scope named results,
                # an already claim-bearing source assertion, and an explicitly
                # user-approved scope exclusion must remain visible to the
                # structural validator and later coverage review.  A declared
                # open problem is the exception: its source kind requires a
                # non-claim disposition.
                source_kind = str(item.get("source_kind") or "").strip().lower()
                preserve_claim_bearing = source_kind != "open_problem" and (
                    item.get("claim_bearing") is True
                    or source_item_is_named_theoretical_statement(item)
                    or configured["scope_disposition"] == "user_approved_scope_exclusion"
                    or isinstance(item.get("user_approved_scope_exclusion"), Mapping)
                )
                # A typed disposition replaces the legacy navigation surface.
                # Old review/auxiliary declaration lists must not silently
                # keep an unselected item in the current semantic graph.  A
                # quarantined defect may retain only the explicitly configured
                # theorem evidence used to validate that defect.
                item.pop("lean_declarations", None)
                item.pop("proof_lean_declarations", None)
                item.pop("support_lean_declarations", None)
                item.pop("support_declarations", None)
                item.pop("source_spec_correspondence", None)
                item["claim_bearing"] = preserve_claim_bearing
                item["inventory_role"] = configured["inventory_role"]
                item["scope_disposition"] = configured["scope_disposition"]
                item["scope_disposition_note"] = configured["reason"]
                if configured["source_status"]:
                    item["source_status"] = configured["source_status"]
                elif configured["source_status_configured"]:
                    item.pop("source_status", None)
                if configured["source_defect_ids"]:
                    item["source_defect_ids"] = configured["source_defect_ids"]
                elif configured["source_defect_ids_configured"]:
                    item.pop("source_defect_ids", None)
                if configured["scope_disposition"] == "user_approved_scope_exclusion":
                    # A retained correction is historical source context, not
                    # an active corrected-target route after this scope choice.
                    item["coverage_status"] = "user_approved_scope_exclusion"
                if configured["support_lean_declarations"]:
                    item["support_lean_declarations"] = configured[
                        "support_lean_declarations"
                    ]
                if configured["subsumed_by_source_item"]:
                    item["subsumed_by_source_item"] = configured[
                        "subsumed_by_source_item"
                    ]
                    item["source_scope_classification"] = (
                        "source_resolved_within_paper_observation"
                    )
                    item["coverage_status"] = "subsumed_by_selected_result"
                    item["protocol_role"] = "subsumed_by_selected_result"
                else:
                    item.pop("subsumed_by_source_item", None)
                continue
            current_role = str(item.get("inventory_role") or "").strip()
            if current_role in {"proof_support", "source_premise_declaration"}:
                item["claim_bearing"] = False
                continue
            if bool(item.get("claim_bearing")) or current_role == "direct_source_target":
                raise PreparationError(
                    f"{key}: unselected source claim needs an explicit unselected_item_dispositions entry"
                )
            item["claim_bearing"] = False
            continue
        item["claim_bearing"] = True
        # A selected result owns a semantic contract, not an inventory-role
        # disposition.  Clear stale role/scope metadata from an earlier
        # incomplete migration before installing the current typed route.
        item.pop("inventory_role", None)
        item.pop("scope_disposition", None)
        item.pop("scope_disposition_note", None)
        # A selected current route cannot retain an earlier deferred-scope
        # record.  Preserve an actual source correction's corrected-target
        # metadata, but clear only the retired scope classification itself.
        if item.get("coverage_status") == "user_approved_scope_exclusion":
            item.pop("coverage_status", None)
        item.pop("user_approved_scope_exclusion", None)
        spec_name = full_name(namespace, interface_module, selected + "Spec")
        evidence_name = (
            evidence_names[selected]
            if semantic_route_schema == 2
            else evidence_names.get(
                selected, existing_evidence_names.get(selected, selected)
            )
        )
        endpoint_name = (
            evidence_name
            if evidence_name.startswith(namespace + ".")
            else full_name(namespace, interface_module, evidence_name)
        )
        item["semantic_contract"] = {
            "spec_declaration": spec_name,
            "evidence_declaration": endpoint_name,
            "evidence_mode": evidence_modes.get(selected, "proves"),
            "semantic_shape": "plain",
        }
        if semantic_route_schema == 2:
            # A schema-2 preparation owns the current source atom and exact
            # Spec/proof route.  Any correspondence record copied from an
            # earlier source bundle describes historical atoms or a prior
            # target; retaining it turns a deliberately pre-graph interface
            # repair into a false typed-obligation failure.  Fresh graph-bound
            # correspondence is issued only after this frozen surface has
            # passed the non-evidentiary semantic preflight.
            item.pop("source_spec_correspondence", None)
        if review_target_kinds.get(selected) == "definition_declaration":
            item["semantic_review_target"] = {
                "schema": 1,
                "kind": "definition_declaration",
                "declaration": spec_name,
            }
        else:
            item.pop("semantic_review_target", None)
        item["lean_declarations"] = [endpoint_name]
        # A checked strengthening is outside the canonical source route, but
        # still a checked support endpoint.  Preparation must retain its
        # declaration identities: otherwise a harmless map regeneration
        # erases that support relation and creates a structural closeout
        # failure before any semantic review can begin.
        support_declarations = [spec_name]
        raw_strengthenings = item.get("checked_strengthening_declarations")
        if isinstance(raw_strengthenings, list):
            retained_strengthenings: list[object] = []
            for raw_strengthening in raw_strengthenings:
                if not isinstance(raw_strengthening, Mapping):
                    retained_strengthenings.append(raw_strengthening)
                    continue
                strengthening_declaration = str(
                    raw_strengthening.get("declaration") or ""
                ).strip()
                strengthening_spec = str(
                    raw_strengthening.get("spec_declaration") or ""
                ).strip()
                if {strengthening_declaration, strengthening_spec} & {
                    endpoint_name,
                    spec_name,
                }:
                    # A former direct route can become the selected literal
                    # core during a map repair. It is no longer a
                    # strengthening, and retaining it in that role makes the
                    # typed map self-contradictory.
                    continue
                retained_strengthenings.append(raw_strengthening)
                for field in ("declaration", "spec_declaration"):
                    declaration = str(raw_strengthening.get(field) or "").strip()
                    if declaration and declaration not in support_declarations:
                        support_declarations.append(declaration)
            if retained_strengthenings:
                item["checked_strengthening_declarations"] = retained_strengthenings
            else:
                item.pop("checked_strengthening_declarations", None)
        item["support_lean_declarations"] = support_declarations
        item.pop("proof_lean_declarations", None)
        # In role schema 2 the source atom's route is the checked theorem or
        # lemma endpoint, while semantic comparison still targets the paired
        # transparent Spec through ``semantic_contract``.  An older schema-1
        # map commonly points this identity field at the Spec itself.  Migrate
        # that routing coordinate mechanically so a role upgrade does not
        # require hand-editing every already-reviewed source atom.
        if semantic_route_schema == 2:
            atoms = item.get("source_claim_atoms")
            if isinstance(atoms, list):
                for atom in atoms:
                    if isinstance(atom, dict):
                        atom["reviewed_lean_route"] = endpoint_name

    _apply_explicit_source_claim_atoms(
        items,
        selected_by_item,
        config,
        folder=folder,
        namespace=namespace,
        interface_module=interface_module,
    )
    _apply_source_core_projections(items, config)
    initialized_atoms = _initialize_selected_source_claim_atoms(
        items,
        selected_by_item,
        config,
        namespace=namespace,
        interface_module=interface_module,
        enabled=config.get("initialize_selected_source_claim_atoms"),
    )
    _apply_model_convention_routes(items, config)
    _apply_approved_review_contexts(items, folder=folder)
    _refresh_current_source_pins(items, folder=folder)

    result = dict(source_map)
    result["items"] = items
    if cited_registry is not None:
        result["cited_source_artifacts_schema"] = 1
        result["cited_source_artifacts"] = cited_registry
    result["approved_review_context_schema"] = 1
    result["semantic_contract_schema"] = 1
    if semantic_route_schema == 2:
        result["semantic_route_schema"] = 2
        result["source_anchor_evidence_required"] = True
    if paper_semantic_prerequisite_sources:
        result["paper_semantic_prerequisite_sources"] = dict(
            sorted(paper_semantic_prerequisite_sources.items())
        )
    else:
        result.pop("paper_semantic_prerequisite_sources", None)
    if library_semantic_prerequisite_sources:
        result["library_semantic_prerequisite_sources"] = dict(
            sorted(library_semantic_prerequisite_sources.items())
        )
    else:
        result.pop("library_semantic_prerequisite_sources", None)
    result["source_spec_correspondence_schema"] = 1
    result["paper_interface_namespace"] = namespace
    if semantic_preflight_import_module:
        result["semantic_preflight_import_module"] = semantic_preflight_import_module
    else:
        result.pop("semantic_preflight_import_module", None)
    if initialized_atoms:
        result["source_claim_atoms_schema"] = 1
    source_version = str(config.get("source_version") or "").strip()
    if source_version:
        result["source_version"] = source_version
    if closeout_review_policy is not None:
        mode = str(result.get("source_coverage_mode") or "").strip()
        if closeout_review_policy.source_scope == CLOSEOUT_SOURCE_SCOPE_ALL_PROSE:
            if mode != "deep_paper_with_all_prose_claims":
                raise PreparationError(
                    "all_prose closeout review policy requires deep_paper_with_all_prose_claims coverage"
                )
        elif mode == "deep_paper_with_all_prose_claims":
            raise PreparationError(
                "named-theory closeout review policy cannot claim a deep all-prose source scope"
            )
        result[CLOSEOUT_REVIEW_POLICY_FIELD] = closeout_review_policy.projection()
    policy = str(result.get("source_inventory_policy") or "").strip()
    v11_policy = (
        "Canonical v11 review binds one transparent PaperInterface Spec to each "
        "selected source claim; retained source claims without a current Spec route "
        "remain explicit audit work rather than disappearing from the inventory."
    )
    policy_without_v11 = policy.replace(v11_policy, " ")
    policy_without_v11 = " ".join(policy_without_v11.split())
    result["source_inventory_policy"] = (
        policy_without_v11 + " " + v11_policy
    ).strip()
    if inventory_review_plan is not None:
        assert folder is not None and prose_presentations is not None
        try:
            result["source_named_result_inventory_review"] = (
                materialize_source_named_result_inventory_review(
                    folder,
                    result,
                    inventory_review_plan,
                    prose_presentations=prose_presentations,
                )
            )
        except SourceInventoryReviewError as error:
            raise PreparationError(str(error)) from error
    return result


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--paper", required=True)
    parser.add_argument("--config", type=Path, required=True)
    parser.add_argument("--write", action="store_true")
    return parser.parse_args()


def main() -> int:
    args = parse_args()
    paper_dir = ROOT / "papers" / args.paper
    try:
        source_map = load_object(paper_dir / "audit" / "paper_statement_map.json", label="source map")
        config = load_object(args.config, label="preparation config")
        prepared = prepare(source_map, config, folder=paper_dir)
    except PreparationError as error:
        print(f"v11 source-map preparation refused: {error}", file=sys.stderr)
        return 1
    selected = len(as_string_list(config.get("include_specs"), label="include_specs"))
    if not args.write:
        print(f"{args.paper}: prepared {selected} canonical v11 source-to-Spec route(s); rerun with --write")
        return 0
    path = paper_dir / "audit" / "paper_statement_map.json"
    path.write_text(json.dumps(prepared, indent=2, ensure_ascii=False) + "\n", encoding="utf-8")
    print(f"{args.paper}: wrote {path} with {selected} canonical v11 source-to-Spec route(s)")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
