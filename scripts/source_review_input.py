"""Exact raw-source bundles used by semantic review.

This module owns no dashboard, Lean, or receipt behavior.  It validates one
paper-local byte-pinned source bundle and derives the stable text/digest inputs
used by semantic reviewers.  Callers that already froze a transaction must pass
its exact byte snapshot; the helper never falls through to live filesystem
bytes in that mode.
"""

from __future__ import annotations

import hashlib
import json
import re
from pathlib import Path
from typing import Any, Mapping

try:
    from scripts.corrected_target_identity import (
        CORRECTED_TARGET_REVIEW_PROTOCOL,
        corrected_target_approval_excerpt_material,
        corrected_target_review_digest,
    )
except ModuleNotFoundError:  # pragma: no cover - direct-script import mode.
    from corrected_target_identity import (
        CORRECTED_TARGET_REVIEW_PROTOCOL,
        corrected_target_approval_excerpt_material,
        corrected_target_review_digest,
    )


SEMANTIC_CONTEXT_ROLES = frozenset(
    {
        "definition",
        "model",
        "model_construction",
        "scope",
        "prior_result",
        "stated_antecedent",
    }
)

APPROVED_REVIEW_CONTEXT_PROTOCOL = "approved-source-review-context-v1"
APPROVED_REVIEW_CONTEXTS_FIELD = "approved_review_contexts"
APPROVED_REVIEW_CONTEXT_SCHEMA_FIELD = "approved_review_context_schema"
MODEL_CONVENTION_REQUIRED_FIELDS = (
    "source_locator",
    "classification",
    "formal_meaning",
    "why_needed",
    "checked_scope",
)
SEMANTIC_SOURCE_ANCHORS_FIELD = "semantic_source_anchor_evidence"

_SOURCE_LOCATOR_IN_TEXT_RE = re.compile(
    r"(?P<path>[^\s;:,]+):(?P<start>[1-9][0-9]*)(?:-(?P<end>[1-9][0-9]*))?"
)


class SourceReviewInputError(ValueError):
    """Raised when an exact paper-local source locator cannot be materialized."""


def normalize_statement(text: str) -> str:
    """Normalize statement text for drift comparisons."""

    return re.sub(r"\s+", " ", text.strip())


def statement_digest(text: str) -> str:
    """Generate the stable normalized digest used by statement receipts."""

    return hashlib.sha256(normalize_statement(text).encode("utf-8")).hexdigest()


def _canonical_digest(value: object) -> str:
    return hashlib.sha256(
        json.dumps(
            value,
            ensure_ascii=True,
            sort_keys=True,
            separators=(",", ":"),
        ).encode("utf-8")
    ).hexdigest()


def _model_convention_index(
    source_proof_fidelity: Mapping[str, Any] | None,
) -> tuple[dict[str, Mapping[str, Any]], str]:
    if not isinstance(source_proof_fidelity, Mapping):
        return {}, "source-proof-fidelity ledger is unavailable"
    raw_conventions = source_proof_fidelity.get("model_conventions")
    if not isinstance(raw_conventions, list):
        return {}, "source-proof-fidelity model_conventions is not a list"
    conventions: dict[str, Mapping[str, Any]] = {}
    for index, raw in enumerate(raw_conventions):
        if not isinstance(raw, Mapping):
            return {}, f"source-proof-fidelity model_conventions[{index}] is not an object"
        context_id = str(raw.get("id") or "").strip()
        if not context_id:
            return {}, f"source-proof-fidelity model_conventions[{index}] has no id"
        if context_id in conventions:
            return {}, f"source-proof-fidelity duplicates model convention `{context_id}`"
        for field in MODEL_CONVENTION_REQUIRED_FIELDS:
            if not str(raw.get(field) or "").strip():
                return {}, f"model convention `{context_id}` lacks `{field}`"
        conventions[context_id] = raw
    return conventions, ""


def materialize_approved_review_contexts(
    source_item: Mapping[str, Any],
    *,
    source_proof_fidelity: Mapping[str, Any] | None,
) -> tuple[list[dict[str, Any]], str]:
    """Resolve existing approval records into one reviewer-visible projection.

    This is a projection, not an inference. Model conventions must be cited by
    stable id from the source map, and additional assumptions must already
    carry their maintainer approval reference. The archival source remains the
    semantic comparison target unless a separate corrected-target record says
    otherwise.
    """

    contexts: list[dict[str, Any]] = []
    raw_ids = source_item.get("model_convention_ids")
    if raw_ids is not None:
        if (
            not isinstance(raw_ids, list)
            or not raw_ids
            or any(not isinstance(value, str) or not value.strip() for value in raw_ids)
            or len({value.strip() for value in raw_ids}) != len(raw_ids)
        ):
            return [], "model_convention_ids must be a nonempty unique string list"
        index, error = _model_convention_index(source_proof_fidelity)
        if error:
            return [], error
        for context_id in sorted(value.strip() for value in raw_ids):
            raw = index.get(context_id)
            if raw is None:
                return [], f"model_convention_ids cites unknown convention `{context_id}`"
            record: dict[str, Any] = {
                "protocol": APPROVED_REVIEW_CONTEXT_PROTOCOL,
                "id": context_id,
                "kind": "source_model_convention",
                **{
                    field: str(raw.get(field) or "").strip()
                    for field in MODEL_CONVENTION_REQUIRED_FIELDS
                },
            }
            report_summary = str(raw.get("report_summary") or "").strip()
            if report_summary:
                record["report_summary"] = report_summary
            record["record_sha256"] = _canonical_digest(record)
            contexts.append(record)

    raw_assumptions = source_item.get("accepted_additional_assumptions")
    if raw_assumptions is not None:
        if not isinstance(raw_assumptions, Mapping):
            return [], "accepted_additional_assumptions is not an object"
        reference = str(raw_assumptions.get("approval_reference") or "").strip()
        approved_at = str(raw_assumptions.get("approved_at") or "").strip()
        conditions_raw = raw_assumptions.get("conditions")
        if (
            not reference
            or not approved_at
            or not isinstance(conditions_raw, list)
            or not conditions_raw
            or any(
                not isinstance(condition, str) or not condition.strip()
                for condition in conditions_raw
            )
        ):
            return [], (
                "accepted_additional_assumptions needs approval_reference, "
                "approved_at, and a nonempty string-list of conditions"
            )
        record = {
            "protocol": APPROVED_REVIEW_CONTEXT_PROTOCOL,
            "id": "accepted_additional_assumptions",
            "kind": "maintainer_approved_additional_assumptions",
            "approval_reference": reference,
            "approved_at": approved_at,
            "conditions": [condition.strip() for condition in conditions_raw],
        }
        record["record_sha256"] = _canonical_digest(record)
        contexts.append(record)
    return contexts, ""


def validated_approved_review_contexts(
    source_item: Mapping[str, Any],
) -> tuple[list[dict[str, Any]], str]:
    """Validate the exact prepared contexts consumed by a semantic reviewer."""

    schema = source_item.get(APPROVED_REVIEW_CONTEXT_SCHEMA_FIELD)
    raw_contexts = source_item.get(APPROVED_REVIEW_CONTEXTS_FIELD)
    if schema is None:
        if raw_contexts is not None:
            return [], "approved review contexts have no schema"
        # Historical source maps remain readable under their recorded engine.
        # The current preparer opts an item into this projection explicitly.
        return [], ""
    if schema != 1:
        return [], f"{APPROVED_REVIEW_CONTEXT_SCHEMA_FIELD} must be 1"
    expected_ids = source_item.get("model_convention_ids")
    has_authority = expected_ids is not None or (
        "accepted_additional_assumptions" in source_item
    )
    if raw_contexts is None:
        if has_authority:
            return [], (
                "source item cites approved semantic context but has no prepared "
                f"{APPROVED_REVIEW_CONTEXTS_FIELD}"
            )
        return [], "approved review context schema has no authority records"
    if not isinstance(raw_contexts, list) or not raw_contexts:
        return [], f"{APPROVED_REVIEW_CONTEXTS_FIELD} must be a nonempty list"
    contexts: list[dict[str, Any]] = []
    seen: set[tuple[str, str]] = set()
    for index, raw in enumerate(raw_contexts):
        if not isinstance(raw, Mapping):
            return [], f"approved review context {index} is not an object"
        record = dict(raw)
        recorded = str(record.pop("record_sha256", "") or "").strip().lower()
        if record.get("protocol") != APPROVED_REVIEW_CONTEXT_PROTOCOL:
            return [], f"approved review context {index} has an unknown protocol"
        context_id = str(record.get("id") or "").strip()
        kind = str(record.get("kind") or "").strip()
        if not context_id or not kind or (kind, context_id) in seen:
            return [], f"approved review context {index} has a missing or duplicate identity"
        if kind == "source_model_convention":
            for field in MODEL_CONVENTION_REQUIRED_FIELDS:
                if not str(record.get(field) or "").strip():
                    return [], f"approved review context `{context_id}` lacks `{field}`"
        elif kind == "maintainer_approved_additional_assumptions":
            conditions = record.get("conditions")
            if (
                not str(record.get("approval_reference") or "").strip()
                or not str(record.get("approved_at") or "").strip()
                or not isinstance(conditions, list)
                or not conditions
                or any(
                    not isinstance(condition, str) or not condition.strip()
                    for condition in conditions
                )
            ):
                return [], (
                    f"approved review context `{context_id}` has malformed "
                    "additional-assumption approval"
                )
        else:
            return [], f"approved review context `{context_id}` has unknown kind `{kind}`"
        if recorded != _canonical_digest(record):
            return [], f"approved review context `{context_id}` has a stale digest"
        record["record_sha256"] = recorded
        contexts.append(record)
        seen.add((kind, context_id))
    model_ids = sorted(
        str(context["id"])
        for context in contexts
        if context.get("kind") == "source_model_convention"
    )
    if expected_ids is not None and model_ids != sorted(
        str(value).strip() for value in expected_ids
    ):
        return [], "approved review contexts do not cover model_convention_ids exactly"
    if "accepted_additional_assumptions" in source_item and not any(
        context.get("kind") == "maintainer_approved_additional_assumptions"
        for context in contexts
    ):
        return [], "approved review contexts omit accepted_additional_assumptions"
    return contexts, ""


def approved_corrected_target_review_context(
    source_item: Mapping[str, Any],
) -> tuple[dict[str, Any] | None, str]:
    """Return one reviewer-visible, approved source-correction target.

    The archival source remains in every semantic-review bundle.  For a
    source item whose printed statement has an explicitly approved correction,
    the reviewer must also see the corrected mathematical target and its
    narrow approval authority; otherwise it can only report the intentional
    literal difference as a mismatch.  This helper is shared by draft
    preflight and the accepting decision queue so the two review stages have
    exactly the same correction semantics.
    """

    status = str(source_item.get("coverage_status") or "").strip()
    if status != "corrected_source_statement":
        return None, ""
    corrected_target = source_item.get("corrected_target")
    if not isinstance(corrected_target, Mapping):
        return None, "corrected source item has no corrected target record"
    statement = str(corrected_target.get("statement") or "").strip()
    source_note = str(source_item.get("source_note") or "").strip()
    approval = corrected_target.get("approval")
    approval_material = corrected_target_approval_excerpt_material(approval)
    target_digest = corrected_target_review_digest(corrected_target)
    recorded_target_digest = str(
        corrected_target.get("corrected_target_review_sha256") or ""
    ).strip().lower()
    if recorded_target_digest and recorded_target_digest != target_digest:
        return None, "approved corrected target has a stale review identity"
    if not statement:
        return None, "approved corrected target has no displayed statement"
    if not source_note:
        return None, "approved corrected target has no scope note"
    if approval_material is None or not isinstance(approval, Mapping):
        return None, "approved corrected target has no exact approval excerpt"
    approval_excerpt, approval_excerpt_sha256 = approval_material
    return {
        "statement": statement,
        "corrected_target_protocol": CORRECTED_TARGET_REVIEW_PROTOCOL,
        "corrected_target_review_sha256": target_digest,
        "archival_equivalence_claimed": corrected_target.get(
            "archival_equivalence_claimed"
        ),
        "archival_source_locator": str(
            corrected_target.get("archival_source_locator") or ""
        ).strip(),
        "governing_defect_ids": list(
            corrected_target.get("governing_defect_ids") or []),
        "scope_note": source_note,
        "approval_record": {
            "kind": str(approval.get("kind") or "").strip(),
            "recorded_at": str(approval.get("recorded_at") or "").strip(),
            "reference": str(approval.get("reference") or "").strip(),
            "artifact_protocol": str(approval.get("artifact_protocol") or "").strip(),
            "artifact_excerpt": approval_excerpt,
            "artifact_excerpt_sha256": approval_excerpt_sha256,
        },
    }, ""


def canonical_source_anchor_evidence(
    folder: Path, source_location: str
) -> list[dict[str, Any]]:
    """Materialize exact byte-pinned excerpts from a paper-local locator bundle.

    This is the sole writer-side constructor for ``source_anchor_evidence``.
    Callers may supply one or more ``relative/path:line[-line]`` locators in a
    descriptive string.  Historical maps use both paper-relative paths such as
    ``source/main.tex`` and repository-relative paths such as
    ``papers/Foo/source/main.tex``; both spellings are accepted only when they
    resolve uniquely to current bytes inside this exact paper folder.  The
    returned representation preserves the authored relative spelling and is
    path- and machine-independent.
    """

    anchors: list[dict[str, Any]] = []
    paper_root = folder.resolve()
    for match in _SOURCE_LOCATOR_IN_TEXT_RE.finditer(source_location):
        raw_path = match.group("path")
        repository_root = paper_root.parents[1]
        candidates = {
            (folder / raw_path).resolve(),
            (repository_root / raw_path).resolve(),
        }
        valid_paths = sorted(
            (
                candidate
                for candidate in candidates
                if candidate.is_relative_to(paper_root) and candidate.is_file()
            ),
            key=lambda candidate: candidate.as_posix(),
        )
        if not valid_paths:
            raise SourceReviewInputError(
                f"source anchor `{raw_path}` is not a readable paper-local file"
            )
        if len(valid_paths) != 1:
            raise SourceReviewInputError(
                f"source anchor `{raw_path}` is ambiguous inside the paper folder"
            )
        path = valid_paths[0]
        try:
            text = (
                path.read_bytes()
                .decode("utf-8")
                .replace("\r\n", "\n")
                .replace("\r", "\n")
            )
        except UnicodeDecodeError as error:
            raise SourceReviewInputError(
                f"source anchor `{raw_path}` is not UTF-8 text"
            ) from error
        lines = text.split("\n")
        if text.endswith("\n"):
            lines.pop()
        start = int(match.group("start"))
        end = int(match.group("end") or start)
        if start > end or end > len(lines):
            raise SourceReviewInputError(
                f"source anchor `{raw_path}:{start}-{end}` is out of range"
            )
        quote = "\n".join(lines[start - 1 : end])
        anchors.append(
            {
                "path": raw_path,
                "line_start": start,
                "line_end": end,
                "quoted_text": quote,
                "quoted_text_sha256": hashlib.sha256(
                    quote.encode("utf-8")
                ).hexdigest(),
            }
        )
    if not anchors:
        raise SourceReviewInputError(
            "source location needs at least one relative file:line anchor"
        )
    return anchors


def _verbatim_anchor_quotes(
    anchors: object,
    *,
    label: str,
) -> tuple[list[str], list[str], str]:
    """Validate and return one ordered raw-source anchor bundle."""

    if not isinstance(anchors, list) or not anchors:
        return [], [], f"{label} has no byte-pinned source_anchor_evidence"
    quotes: list[str] = []
    quote_digests: list[str] = []
    for index, raw_anchor in enumerate(anchors):
        if not isinstance(raw_anchor, Mapping):
            return [], [], f"{label} source anchor {index} is not an object"
        quote = raw_anchor.get("quoted_text")
        recorded = str(raw_anchor.get("quoted_text_sha256") or "").strip().lower()
        if not isinstance(quote, str) or not quote:
            return [], [], f"{label} source anchor {index} has no quoted_text"
        normalized = quote.replace("\r\n", "\n").replace("\r", "\n")
        # PDF-to-text and TeX extraction can legitimately retain C0 layout
        # controls.  Exact source anchors already authenticate those bytes with
        # the independently checked quote digest and source-file comparison;
        # refusing a valid byte-pinned excerpt here would turn extraction
        # typography into a semantic-review blocker.  Keep the raw text (and
        # therefore its identity) unchanged.  JSON renderers escape these
        # controls for reviewer display without paraphrasing the source.
        actual = hashlib.sha256(normalized.encode("utf-8")).hexdigest()
        if not re.fullmatch(r"[0-9a-f]{64}", recorded) or recorded != actual:
            return [], [], f"{label} source anchor {index} quoted_text_sha256 is stale"
        quotes.append(normalized)
        quote_digests.append(actual)
    return quotes, quote_digests, ""


def _semantic_anchor_evidence(
    source_item: Mapping[str, Any],
) -> tuple[object, str]:
    """Select the exact source excerpt appropriate for semantic comparison.

    Source coverage deliberately pins a conservative span around every visible
    presentation.  When PDF/TeX extraction carries explanatory prose past the
    completed displayed statement, a curator may additionally pin one exact
    statement core.  That core narrows only the reviewer input; it never
    replaces the full source-coverage anchor or its byte check.
    """

    semantic_anchors = source_item.get(SEMANTIC_SOURCE_ANCHORS_FIELD)
    if semantic_anchors is None:
        return source_item.get("source_anchor_evidence"), ""
    if not isinstance(semantic_anchors, list) or len(semantic_anchors) != 1:
        return (
            [],
            f"{SEMANTIC_SOURCE_ANCHORS_FIELD} must be a one-item exact source-anchor list",
        )
    semantic_anchor = semantic_anchors[0]
    coverage_anchors = source_item.get("source_anchor_evidence")
    if not isinstance(semantic_anchor, Mapping) or not isinstance(coverage_anchors, list):
        return (
            [],
            f"{SEMANTIC_SOURCE_ANCHORS_FIELD} requires ordinary source_anchor_evidence",
        )
    path = str(semantic_anchor.get("path") or "").strip()
    start = semantic_anchor.get("line_start")
    end = semantic_anchor.get("line_end")
    contained = any(
        isinstance(coverage, Mapping)
        and coverage.get("path") == path
        and isinstance(coverage.get("line_start"), int)
        and isinstance(coverage.get("line_end"), int)
        and isinstance(start, int)
        and isinstance(end, int)
        and coverage["line_start"] <= start <= end <= coverage["line_end"]
        for coverage in coverage_anchors
    )
    if not contained:
        return (
            [],
            f"{SEMANTIC_SOURCE_ANCHORS_FIELD} must be contained in an ordinary "
            "source-coverage anchor",
        )
    return semantic_anchors, ""


def source_semantic_input_bundle(
    source_item: Mapping[str, Any],
    *,
    require_context_roles: bool = False,
    include_approved_contexts: bool = True,
) -> tuple[str, str, str]:
    """Return verbatim source text and its exact semantic-input identity.

    The optional approval projection is reviewer guidance, not archival source
    text.  Callers that need to distinguish an unchanged source/Lean judgment
    from a newly attached maintainer clarification may request the stable
    anchor-only identity with ``include_approved_contexts=False``.  The normal
    review input still binds the approval projection, so a new reviewer always
    sees it.
    """

    semantic_anchors, anchor_error = _semantic_anchor_evidence(source_item)
    if anchor_error:
        return "", "", anchor_error
    quotes, quote_digests, error = _verbatim_anchor_quotes(
        semantic_anchors, label="source item"
    )
    if error:
        return "", "", error
    requirements = source_item.get("semantic_context_requirements")
    if requirements is not None:
        if not isinstance(requirements, list):
            return "", "", "semantic_context_requirements is not a list"
        for index, requirement in enumerate(requirements):
            if not isinstance(requirement, Mapping):
                return "", "", f"semantic context {index} is not an object"
            if require_context_roles:
                role = str(requirement.get("semantic_role") or "").strip()
                if role not in SEMANTIC_CONTEXT_ROLES:
                    return (
                        "",
                        "",
                        f"semantic context {index} has no permitted semantic_role",
                    )
            context_quotes, context_digests, context_error = _verbatim_anchor_quotes(
                requirement.get("source_anchor_evidence"),
                label=f"semantic context {index}",
            )
            if context_error:
                return "", "", context_error
            quotes.extend(context_quotes)
            quote_digests.extend(context_digests)
    identity_payload: dict[str, Any] = {
        "schema": 1,
        "source_anchor_quote_sha256": quote_digests,
    }
    if include_approved_contexts:
        approved_contexts, context_error = validated_approved_review_contexts(
            source_item
        )
        if context_error:
            return "", "", context_error
    else:
        approved_contexts = []
    if approved_contexts:
        identity_payload = {
            "schema": 2,
            "source_anchor_quote_sha256": quote_digests,
            "approved_review_context_sha256": [
                context["record_sha256"] for context in approved_contexts
            ],
        }
    identity = hashlib.sha256(
        json.dumps(
            identity_payload,
            ensure_ascii=True,
            sort_keys=True,
            separators=(",", ":"),
        ).encode("utf-8")
    ).hexdigest()
    return "\n\n[Next verbatim source excerpt]\n\n".join(quotes), identity, ""


def _snapshot_bytes(
    path: Path,
    *,
    file_bytes_override: Mapping[Path, bytes | None] | None,
) -> bytes:
    """Read one path, refusing live fallback when a transaction is frozen."""

    if file_bytes_override is None:
        return path.read_bytes()
    normalized = {candidate.resolve(): value for candidate, value in file_bytes_override.items()}
    resolved = path.resolve()
    if resolved not in normalized or normalized[resolved] is None:
        raise OSError("path is absent from the frozen transaction")
    value = normalized[resolved]
    assert value is not None
    return value


def source_anchor_file_error(
    folder: Path,
    source_record: Mapping[str, Any],
    *,
    repository_root: Path | None = None,
    file_bytes_override: Mapping[Path, bytes | None] | None = None,
) -> str:
    """Verify every raw anchor against current or transaction-frozen bytes."""

    anchors = source_record.get("source_anchor_evidence")
    if not isinstance(anchors, list) or not anchors:
        return "no byte-pinned source_anchor_evidence is registered"
    anchor_sets: list[tuple[str, list[object]]] = [("source anchor", anchors)]
    semantic_anchors = source_record.get(SEMANTIC_SOURCE_ANCHORS_FIELD)
    if semantic_anchors is not None:
        if not isinstance(semantic_anchors, list) or len(semantic_anchors) != 1:
            return (
                f"{SEMANTIC_SOURCE_ANCHORS_FIELD} must be a one-item exact "
                "source-anchor list"
            )
        anchor_sets.append(("semantic source anchor", semantic_anchors))
    paper_root = folder.resolve()
    repo_root = (
        repository_root.resolve()
        if repository_root is not None
        else folder.resolve().parents[1]
    )
    frozen_paths = (
        {
            candidate.resolve()
            for candidate, value in file_bytes_override.items()
            if value is not None
        }
        if file_bytes_override is not None
        else set()
    )
    for label_prefix, anchor_set in anchor_sets:
        for index, raw_anchor in enumerate(anchor_set):
            label = f"{label_prefix} {index}"
            if not isinstance(raw_anchor, Mapping):
                return label + " is not an object"
            raw_path = str(raw_anchor.get("path") or "").strip()
            start = raw_anchor.get("line_start")
            end = raw_anchor.get("line_end")
            quote = raw_anchor.get("quoted_text")
            if (
                not raw_path
                or not isinstance(start, int)
                or isinstance(start, bool)
                or not isinstance(end, int)
                or isinstance(end, bool)
                or start <= 0
                or end < start
                or not isinstance(quote, str)
                or not quote
            ):
                return label + " lacks a valid path, line range, or quote"
            candidates = [(folder / raw_path).resolve()]
            repository_candidate = (repo_root / raw_path).resolve()
            if repository_candidate not in candidates:
                candidates.append(repository_candidate)
            path = next(
                (
                    candidate
                    for candidate in candidates
                    if candidate.is_relative_to(paper_root)
                    and (
                        candidate in frozen_paths
                        if file_bytes_override is not None
                        else candidate.is_file()
                    )
                ),
                candidates[0],
            )
            try:
                path.relative_to(paper_root)
                raw_bytes = _snapshot_bytes(
                    path, file_bytes_override=file_bytes_override
                )
                lines = (
                    raw_bytes.decode("utf-8")
                    .replace("\r\n", "\n")
                    .replace("\r", "\n")
                    .split("\n")
                )
            except (OSError, UnicodeDecodeError, ValueError) as exc:
                return label + " cannot read the declared source path: " + str(exc)
            if end > len(lines) - (1 if lines and lines[-1] == "" else 0):
                return label + " line range is outside the declared source file"
            actual = "\n".join(lines[start - 1 : end])
            normalized_quote = quote.replace("\r\n", "\n").replace("\r", "\n")
            if actual != normalized_quote:
                return label + " quote does not equal the current declared source slice"
    return ""
