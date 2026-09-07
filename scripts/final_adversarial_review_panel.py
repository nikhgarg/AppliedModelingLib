#!/usr/bin/env python3
"""Validate independent final-adversary reviews for one frozen surface.

Historical closeouts used one conventional ``AGENT_SOURCE_AUDIT.md`` file.
Policy-aware closeouts instead record a small paper-local panel whose entries
bind distinct reviewer identities and immutable audit documents to the exact
one-review comparison surface.  Increasing panel cardinality can therefore
retain every already valid review of unchanged comparison material.
"""

from __future__ import annotations

import hashlib
import json
import re
from collections.abc import Mapping
from dataclasses import dataclass
from pathlib import Path, PurePosixPath

from scripts.formalization_protocol import (
    FormalizationProtocolError,
    resolve_closeout_review_policy_assurance,
)


FINAL_ADVERSARIAL_REVIEW_PANEL_SCHEMA = 1
FINAL_ADVERSARIAL_REVIEW_PANEL_RELATIVE_PATH = Path(
    "docs/FINAL_ADVERSARIAL_REVIEW_PANEL.json"
)
PRIMARY_FINAL_ADVERSARIAL_AUDIT_RELATIVE_PATH = Path(
    "docs/AGENT_SOURCE_AUDIT.md"
)
FINAL_ADVERSARIAL_REVIEW_SCOPE = "complete_current_surface"

_SHA256_RE = re.compile(r"^[0-9a-f]{64}$")
_ISO_UTC_RE = re.compile(
    r"^\d{4}-\d{2}-\d{2}T\d{2}:\d{2}:\d{2}(?:\.\d+)?Z$"
)
_AUDIT_STATUS_RE = re.compile(
    r"^##[ \t]+Overall status:[ \t]*([^\r\n]*?)[ \t]*\r?$", re.M
)
_AUDIT_SCAFFOLD_RE = re.compile(
    r"NEEDS AGENT REVIEW|scaffold has not performed", re.I
)
_SURFACE_TARGET_RE = re.compile(
    r"(?mi)^\s*-\s*Reviewed final holistic audit surface identity:\s*"
    r"`([0-9a-f]{64})`\s*$"
)
_COMPLETE_SCOPE_RE = re.compile(
    r"(?mi)^\s*-\s*Final audit scope:\s*"
    r"`complete_current_surface`\s*$"
)
_SCOPE_RE = re.compile(
    r"(?mi)^[ \t]*(?:-[ \t]*)?Final audit scope:[ \t]*([^\r\n]*)$"
)
_LEGACY_PLAN_RE = re.compile(
    r"(?mi)^\s*-\s*Reviewed closeout plan identity:\s*"
    r"`([0-9a-f]{64})`\s*$"
)


class FinalAdversarialReviewPanelError(ValueError):
    """The panel artifact is malformed or does not meet frozen policy."""


@dataclass(frozen=True)
class FinalAdversarialReviewPanelFinding:
    """One exact panel or member-audit failure."""

    path: Path
    message: str


def audit_text_attestation_errors(
    text: str,
    *,
    target_surface_identity: str = "",
    require_surface_binding: bool = False,
    allow_historical_missing_scope: bool = False,
) -> tuple[str, ...]:
    """Check one review document's verdict and exact-surface attestation."""

    errors: list[str] = []
    statuses = _AUDIT_STATUS_RE.findall(text)
    if set(statuses) != {"PASS"}:
        errors.append(
            "must record `## Overall status: PASS` without conflicting overall "
            "verdicts"
        )
    if _AUDIT_SCAFFOLD_RE.search(text):
        errors.append("is still a scaffold, not a completed holistic audit")
    targets = _SURFACE_TARGET_RE.findall(text)
    legacy_targets = _LEGACY_PLAN_RE.findall(text)
    target = target_surface_identity.strip().lower()
    if target:
        if targets != [target]:
            errors.append(
                "does not bind the exact current final holistic audit surface "
                f"identity `{target}`"
            )
        scopes = _SCOPE_RE.findall(text)
        complete_scope = len(scopes) == 1 and _COMPLETE_SCOPE_RE.search(text)
        historical_missing_scope = allow_historical_missing_scope and not scopes
        if not complete_scope and not historical_missing_scope:
            errors.append(
                "must attest `Final audit scope: complete_current_surface` for "
                "terminal closeout; a bounded repair recheck is not terminal evidence"
            )
    elif require_surface_binding and len(targets) + len(legacy_targets) != 1:
        errors.append("must contain exactly one valid final-audit identity binding")
    return tuple(errors)


def _load_json_without_duplicate_keys(path: Path) -> object:
    def object_from_pairs(pairs: list[tuple[str, object]]) -> dict[str, object]:
        result: dict[str, object] = {}
        for key, value in pairs:
            if key in result:
                raise FinalAdversarialReviewPanelError(
                    f"duplicate JSON key `{key}`"
                )
            result[key] = value
        return result

    try:
        return json.loads(
            path.read_text(encoding="utf-8"),
            object_pairs_hook=object_from_pairs,
        )
    except (OSError, UnicodeError, json.JSONDecodeError) as exc:
        raise FinalAdversarialReviewPanelError(str(exc)) from exc


def _paper_local_markdown_path(value: object, *, field: str) -> PurePosixPath:
    if not isinstance(value, str) or not value.strip() or value != value.strip():
        raise FinalAdversarialReviewPanelError(
            f"{field} must be a normalized paper-local Markdown path"
        )
    path = PurePosixPath(value)
    if (
        path.is_absolute()
        or not path.parts
        or path.parts[0] != "docs"
        or any(part in {"", ".", ".."} for part in path.parts)
        or path.suffix.lower() != ".md"
        or path.as_posix() != value
    ):
        raise FinalAdversarialReviewPanelError(
            f"{field} must be a normalized paper-local `docs/*.md` path"
        )
    return path


def _validated_panel_rows(
    folder: Path,
    *,
    target_surface_identity: str,
    review_policy_assurance: Mapping[str, object],
) -> tuple[tuple[PurePosixPath, ...], tuple[FinalAdversarialReviewPanelFinding, ...]]:
    panel_path = folder / FINAL_ADVERSARIAL_REVIEW_PANEL_RELATIVE_PATH
    findings: list[FinalAdversarialReviewPanelFinding] = []
    if not panel_path.is_file():
        return (), (
            FinalAdversarialReviewPanelFinding(
                panel_path,
                "policy-aware closeout is missing "
                "`docs/FINAL_ADVERSARIAL_REVIEW_PANEL.json`",
            ),
        )
    try:
        panel_path.resolve().relative_to(folder.resolve())
    except (OSError, RuntimeError, ValueError):
        return (), (
            FinalAdversarialReviewPanelFinding(
                panel_path,
                "final-adversary review panel resolves outside its paper folder",
            ),
        )
    try:
        panel = _load_json_without_duplicate_keys(panel_path)
    except FinalAdversarialReviewPanelError as exc:
        return (), (
            FinalAdversarialReviewPanelFinding(
                panel_path, "final-adversary review panel is unreadable: " + str(exc)
            ),
        )
    if not isinstance(panel, Mapping):
        return (), (
            FinalAdversarialReviewPanelFinding(
                panel_path, "final-adversary review panel must be an object"
            ),
        )
    required_fields = {
        "schema",
        "paper",
        "review_material_sha256",
        "required_reviewer_count",
        "reviews",
    }
    allowed_fields = required_fields | {"ineligible_reviewer_identities"}
    if not required_fields <= set(panel) or not set(panel) <= allowed_fields:
        return (), (
            FinalAdversarialReviewPanelFinding(
                panel_path, "final-adversary review panel fields are malformed"
            ),
        )
    if (
        isinstance(panel.get("schema"), bool)
        or panel.get("schema") != FINAL_ADVERSARIAL_REVIEW_PANEL_SCHEMA
    ):
        findings.append(
            FinalAdversarialReviewPanelFinding(
                panel_path, "final-adversary review panel schema must be 1"
            )
        )
    if panel.get("paper") != folder.name:
        findings.append(
            FinalAdversarialReviewPanelFinding(
                panel_path, "final-adversary review panel belongs to another paper"
            )
        )
    target = target_surface_identity.strip().lower()
    if not _SHA256_RE.fullmatch(target):
        findings.append(
            FinalAdversarialReviewPanelFinding(
                panel_path, "frozen final holistic review material identity is malformed"
            )
        )
    if panel.get("review_material_sha256") != target:
        findings.append(
            FinalAdversarialReviewPanelFinding(
                panel_path,
                "final-adversary review panel does not bind the exact frozen "
                f"review material identity `{target}`",
            )
        )
    try:
        policy = resolve_closeout_review_policy_assurance(review_policy_assurance)
    except FormalizationProtocolError as exc:
        findings.append(
            FinalAdversarialReviewPanelFinding(
                panel_path, "frozen review-policy assurance is malformed: " + str(exc)
            )
        )
        return (), tuple(findings)
    required_count = policy.required_final_adversary_count
    raw_recorded_count = panel.get("required_reviewer_count")
    if (
        isinstance(raw_recorded_count, bool)
        or raw_recorded_count != required_count
    ):
        findings.append(
            FinalAdversarialReviewPanelFinding(
                panel_path,
                "final-adversary review panel records reviewer count "
                f"`{raw_recorded_count}` but frozen policy requires `{required_count}`",
            )
        )
    raw_ineligible = panel.get("ineligible_reviewer_identities", [])
    if not isinstance(raw_ineligible, list) or any(
        not isinstance(value, str) or not value.strip() or value != value.strip()
        for value in raw_ineligible
    ):
        findings.append(
            FinalAdversarialReviewPanelFinding(
                panel_path,
                "ineligible_reviewer_identities must be a duplicate-free list of "
                "stable nonempty identities",
            )
        )
        ineligible: set[str] = set()
    else:
        ineligible = set(raw_ineligible)
        if len(ineligible) != len(raw_ineligible):
            findings.append(
                FinalAdversarialReviewPanelFinding(
                    panel_path,
                    "ineligible_reviewer_identities must not contain duplicates",
                )
            )

    raw_reviews = panel.get("reviews")
    if not isinstance(raw_reviews, list):
        findings.append(
            FinalAdversarialReviewPanelFinding(
                panel_path, "final-adversary review panel reviews must be a list"
            )
        )
        return (), tuple(findings)
    reviewer_ids: set[str] = set()
    audit_paths: set[PurePosixPath] = set()
    valid_paths: list[PurePosixPath] = []
    review_fields = {
        "reviewer_identity",
        "audit_artifact_path",
        "audit_artifact_sha256",
        "reviewed_surface_sha256",
        "judgment",
        "scope",
        "reviewed_at",
        "independence",
    }
    for index, raw_review in enumerate(raw_reviews):
        label = f"reviews[{index}]"
        if not isinstance(raw_review, Mapping) or set(raw_review) != review_fields:
            findings.append(
                FinalAdversarialReviewPanelFinding(
                    panel_path, f"{label} fields are malformed"
                )
            )
            continue
        reviewer = raw_review.get("reviewer_identity")
        if (
            not isinstance(reviewer, str)
            or not reviewer.strip()
            or reviewer != reviewer.strip()
        ):
            findings.append(
                FinalAdversarialReviewPanelFinding(
                    panel_path, f"{label}.reviewer_identity must be a stable nonempty identity"
                )
            )
            reviewer = ""
        elif reviewer in reviewer_ids:
            findings.append(
                FinalAdversarialReviewPanelFinding(
                    panel_path, f"reviewer identity `{reviewer}` is duplicated"
                )
            )
        else:
            reviewer_ids.add(reviewer)
            if reviewer in ineligible:
                findings.append(
                    FinalAdversarialReviewPanelFinding(
                        panel_path,
                        f"reviewer identity `{reviewer}` is recorded as an author, "
                        "implementer, or semantic reviewer and is not independent",
                    )
                )
        try:
            relative_path = _paper_local_markdown_path(
                raw_review.get("audit_artifact_path"),
                field=f"{label}.audit_artifact_path",
            )
        except FinalAdversarialReviewPanelError as exc:
            findings.append(FinalAdversarialReviewPanelFinding(panel_path, str(exc)))
            continue
        if relative_path in audit_paths:
            findings.append(
                FinalAdversarialReviewPanelFinding(
                    panel_path,
                    f"audit artifact path `{relative_path.as_posix()}` is duplicated",
                )
            )
        else:
            audit_paths.add(relative_path)
        if raw_review.get("reviewed_surface_sha256") != target:
            findings.append(
                FinalAdversarialReviewPanelFinding(
                    panel_path,
                    f"{label} does not attest the exact frozen review material "
                    f"identity `{target}`",
                )
            )
        if raw_review.get("judgment") != "PASS":
            findings.append(
                FinalAdversarialReviewPanelFinding(
                    panel_path, f"{label}.judgment must be `PASS`"
                )
            )
        if raw_review.get("scope") != FINAL_ADVERSARIAL_REVIEW_SCOPE:
            findings.append(
                FinalAdversarialReviewPanelFinding(
                    panel_path,
                    f"{label}.scope must be `{FINAL_ADVERSARIAL_REVIEW_SCOPE}`",
                )
            )
        reviewed_at = raw_review.get("reviewed_at")
        if not isinstance(reviewed_at, str) or not _ISO_UTC_RE.fullmatch(reviewed_at):
            findings.append(
                FinalAdversarialReviewPanelFinding(
                    panel_path, f"{label}.reviewed_at must be an ISO-like UTC timestamp"
                )
            )
        independence = raw_review.get("independence")
        if (
            not isinstance(independence, Mapping)
            or set(independence)
            != {"did_not_author_or_repair", "did_not_issue_semantic_judgments"}
            or independence.get("did_not_author_or_repair") is not True
            or independence.get("did_not_issue_semantic_judgments") is not True
        ):
            findings.append(
                FinalAdversarialReviewPanelFinding(
                    panel_path,
                    f"{label}.independence must attest both author/repair and "
                    "semantic-judgment independence",
                )
            )
        artifact = folder / relative_path
        try:
            artifact.resolve().relative_to(folder.resolve())
        except (OSError, RuntimeError, ValueError):
            findings.append(
                FinalAdversarialReviewPanelFinding(
                    artifact,
                    "final-adversary audit artifact resolves outside its paper folder",
                )
            )
            continue
        try:
            artifact_bytes = artifact.read_bytes()
            artifact_text = artifact_bytes.decode("utf-8")
        except (OSError, UnicodeError) as exc:
            findings.append(
                FinalAdversarialReviewPanelFinding(
                    artifact, f"final-adversary audit artifact is unreadable: {exc}"
                )
            )
            continue
        recorded_digest = raw_review.get("audit_artifact_sha256")
        actual_digest = hashlib.sha256(artifact_bytes).hexdigest()
        if not isinstance(recorded_digest, str) or not _SHA256_RE.fullmatch(
            recorded_digest
        ):
            findings.append(
                FinalAdversarialReviewPanelFinding(
                    panel_path, f"{label}.audit_artifact_sha256 must be a lowercase SHA-256"
                )
            )
        elif recorded_digest != actual_digest:
            findings.append(
                FinalAdversarialReviewPanelFinding(
                    artifact,
                    "final-adversary audit artifact does not match its recorded SHA-256",
                )
            )
        for message in audit_text_attestation_errors(
            artifact_text, target_surface_identity=target
        ):
            findings.append(
                FinalAdversarialReviewPanelFinding(
                    artifact, "final-adversary audit artifact " + message
                )
            )
        valid_paths.append(relative_path)

    if len(raw_reviews) < required_count:
        missing = required_count - len(raw_reviews)
        findings.append(
            FinalAdversarialReviewPanelFinding(
                panel_path,
                f"final-adversary review panel needs {missing} additional distinct "
                f"reviewer{'s' if missing != 1 else ''} for the unchanged review material",
            )
        )
    if raw_reviews and PRIMARY_FINAL_ADVERSARIAL_AUDIT_RELATIVE_PATH not in audit_paths:
        findings.append(
            FinalAdversarialReviewPanelFinding(
                panel_path,
                "final-adversary review panel must retain the primary "
                "`docs/AGENT_SOURCE_AUDIT.md` audit",
            )
        )
    return tuple(valid_paths), tuple(findings)


def final_adversarial_review_panel_errors(
    folder: Path,
    *,
    target_surface_identity: str,
    review_policy_assurance: Mapping[str, object],
) -> tuple[FinalAdversarialReviewPanelFinding, ...]:
    """Return all panel failures for one authenticated policy assurance."""

    _, findings = _validated_panel_rows(
        folder,
        target_surface_identity=target_surface_identity,
        review_policy_assurance=review_policy_assurance,
    )
    return findings


def validated_final_adversarial_review_artifact_paths(
    folder: Path,
    *,
    target_surface_identity: str,
    review_policy_assurance: Mapping[str, object],
) -> tuple[Path, ...]:
    """Return all immutable panel/audit paths after complete validation."""

    relative_paths, findings = _validated_panel_rows(
        folder,
        target_surface_identity=target_surface_identity,
        review_policy_assurance=review_policy_assurance,
    )
    if findings:
        raise FinalAdversarialReviewPanelError(
            "; ".join(finding.message for finding in findings)
        )
    return (
        folder / FINAL_ADVERSARIAL_REVIEW_PANEL_RELATIVE_PATH,
        *(folder / path for path in relative_paths),
    )
