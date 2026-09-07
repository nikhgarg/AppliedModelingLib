"""Content-addressed receipts for cache-free saved paper-status evidence."""

from __future__ import annotations

import hashlib
import json
import re
from dataclasses import dataclass
from pathlib import Path, PurePosixPath
from typing import Any, Mapping

try:
    from lean_import_closure import (
        WorktreeImportClosureProvider,
        lean_import_closure_payload_sha256,
        validated_lean_import_closure_payload,
    )
    from source_coverage_scope import (
        SOURCE_ITEM_COVERAGE_DIGEST_SCHEMA,
        source_coverage_mode_from_map,
        source_item_coverage_receipt_matches,
        source_item_coverage_sha256,
    )
except ModuleNotFoundError:  # pragma: no cover - supports module-style imports.
    from scripts.lean_import_closure import (
        WorktreeImportClosureProvider,
        lean_import_closure_payload_sha256,
        validated_lean_import_closure_payload,
    )
    from scripts.source_coverage_scope import (
        SOURCE_ITEM_COVERAGE_DIGEST_SCHEMA,
        source_coverage_mode_from_map,
        source_item_coverage_receipt_matches,
        source_item_coverage_sha256,
    )


SAVED_STATUS_REUSE_RECEIPT_SCHEMA = 3
STATEMENT_DISPOSITION_SCHEMA = 2
COVERAGE_DISPOSITION_SCHEMA = 1
CANONICAL_SOURCE_ATTESTATION_SCHEMA = 1
CANONICAL_SOURCE_PIN_VALIDATOR_ID = "saved-status-canonical-source-pin/v1"
SHA256_RE = re.compile(r"^[0-9a-f]{64}$")

DIRECT_COVERAGE = frozenset({"covered", "covered_by_rows"})
CORRECTED_COVERAGE = "covered_corrected_target"
BOUNDARY_COVERAGE = frozenset(
    {"conditional_boundary", "covered_with_boundary", "visible_premise_boundary"}
)
SUPPORT_COVERAGE = frozenset({"covered_by_support", "support_only"})
OUT_OF_SCOPE_COVERAGE = frozenset(
    {
        "out_of_scope",
        "not_a_paper_target",
        "not_a_theorem_statement",
        "user_approved_scope_exclusion",
    }
)
APPROVED_COVERAGE_AUDIT_KINDS = frozenset(
    {"source_to_dashboard_llm", "source_to_dashboard_agent"}
)


@dataclass(frozen=True)
class SavedStatusReuseProblem:
    lane: str
    reason: str

    def format(self) -> str:
        return f"{self.lane}: {self.reason}"


@dataclass(frozen=True)
class SavedStatusDisposition:
    sha256: str
    counts: Mapping[str, int]
    source_bindings: tuple[Mapping[str, str], ...] = ()


@dataclass(frozen=True)
class SavedStatusReuseReceipt:
    lean_candidate_closure: Mapping[str, object]
    lean_candidate_closure_sha256: str
    statement_disposition_sha256: str
    coverage_disposition_sha256: str
    canonical_source_attestation: Mapping[str, object]
    coverage_source_bindings: tuple[Mapping[str, str], ...]
    statement_counts: Mapping[str, int]
    coverage_counts: Mapping[str, int]
    canonical_source_state: str = "verified_current_bytes"

    def as_dict(self) -> dict[str, object]:
        return {
            "schema": SAVED_STATUS_REUSE_RECEIPT_SCHEMA,
            "lean_candidate_closure": dict(self.lean_candidate_closure),
            "lean_candidate_closure_sha256": self.lean_candidate_closure_sha256,
            "statement_disposition_sha256": self.statement_disposition_sha256,
            "coverage_disposition_sha256": self.coverage_disposition_sha256,
            "canonical_source_attestation": dict(self.canonical_source_attestation),
            "coverage_source_bindings": [
                dict(binding) for binding in self.coverage_source_bindings
            ],
            "statement_counts": dict(self.statement_counts),
            "coverage_counts": dict(self.coverage_counts),
        }

    @property
    def sha256(self) -> str:
        return stable_sha256({"saved_status_reuse_receipt": self.as_dict()})


def validated_saved_status_reuse_receipt(value: object) -> dict[str, object]:
    """Validate one portable receipt, including its Lean-owned source set."""

    expected = {
        "schema",
        "lean_candidate_closure",
        "lean_candidate_closure_sha256",
        "statement_disposition_sha256",
        "coverage_disposition_sha256",
        "canonical_source_attestation",
        "coverage_source_bindings",
        "statement_counts",
        "coverage_counts",
    }
    if not isinstance(value, Mapping) or set(value) != expected:
        raise ValueError("saved-status reuse receipt fields are malformed")
    if value.get("schema") != SAVED_STATUS_REUSE_RECEIPT_SCHEMA:
        raise ValueError("saved-status reuse receipt schema is unsupported")
    closure = validated_lean_import_closure_payload(value.get("lean_candidate_closure"))
    closure_sha256 = _sha256(value.get("lean_candidate_closure_sha256"))
    statement_sha256 = _sha256(value.get("statement_disposition_sha256"))
    coverage_sha256 = _sha256(value.get("coverage_disposition_sha256"))
    canonical_source_attestation = _validated_canonical_source_attestation(
        value.get("canonical_source_attestation")
    )
    bindings = _validated_coverage_source_bindings(
        value.get("coverage_source_bindings")
    )
    statement_counts = _validated_counts(
        value.get("statement_counts"),
        keys={
            "total",
            "matches",
            "mismatch",
            "formalization_boundary",
            "uncertain",
            "unknown",
            "source_condition_rows",
        },
        lane="statement",
    )
    coverage_counts = _validated_counts(
        value.get("coverage_counts"),
        keys={
            "total",
            "covered",
            "corrected_target_covered",
            "conditional_boundary",
            "support_only",
            "out_of_scope",
            "scope_exclusion",
        },
        lane="coverage",
    )
    if (
        not closure_sha256
        or closure_sha256 != lean_import_closure_payload_sha256(closure)
        or not statement_sha256
        or not coverage_sha256
    ):
        raise ValueError("saved-status reuse receipt identity is invalid")
    return {
        "schema": SAVED_STATUS_REUSE_RECEIPT_SCHEMA,
        "lean_candidate_closure": closure,
        "lean_candidate_closure_sha256": closure_sha256,
        "statement_disposition_sha256": statement_sha256,
        "coverage_disposition_sha256": coverage_sha256,
        "canonical_source_attestation": canonical_source_attestation,
        "coverage_source_bindings": bindings,
        "statement_counts": statement_counts,
        "coverage_counts": coverage_counts,
    }


def stable_sha256(value: object) -> str:
    encoded = json.dumps(
        value,
        ensure_ascii=False,
        sort_keys=True,
        separators=(",", ":"),
    ).encode("utf-8")
    return hashlib.sha256(encoded).hexdigest()


def _sha256(value: object) -> str:
    text = str(value or "").strip().lower()
    return text if SHA256_RE.fullmatch(text) else ""


def _validated_canonical_source_attestation(value: object) -> dict[str, object]:
    expected_fields = {
        "schema",
        "source_artifact_path",
        "expected_sha256",
        "observed_sha256",
        "byte_length",
        "validator",
    }
    if not isinstance(value, Mapping) or set(value) != expected_fields:
        raise ValueError("saved canonical-source attestation fields are malformed")
    raw_path = str(value.get("source_artifact_path") or "").strip()
    pure_path = PurePosixPath(raw_path)
    expected = _sha256(value.get("expected_sha256"))
    observed = _sha256(value.get("observed_sha256"))
    byte_length = value.get("byte_length")
    if (
        value.get("schema") != CANONICAL_SOURCE_ATTESTATION_SCHEMA
        or not raw_path
        or pure_path.is_absolute()
        or ".." in pure_path.parts
        or expected != observed
        or not expected
        or not isinstance(byte_length, int)
        or isinstance(byte_length, bool)
        or byte_length < 0
        or value.get("validator") != CANONICAL_SOURCE_PIN_VALIDATOR_ID
    ):
        raise ValueError("saved canonical-source attestation is invalid")
    return {
        "schema": CANONICAL_SOURCE_ATTESTATION_SCHEMA,
        "source_artifact_path": pure_path.as_posix(),
        "expected_sha256": expected,
        "observed_sha256": observed,
        "byte_length": byte_length,
        "validator": CANONICAL_SOURCE_PIN_VALIDATOR_ID,
    }


def _current_canonical_source_attestation(
    root: Path,
    folder: Path,
    *,
    baseline_attestation: object | None,
) -> tuple[dict[str, object] | None, str, str]:
    """Verify current canonical bytes or reuse one immutable issuance receipt.

    A fresh ledger can only be issued with present bytes whose whole-file hash
    matches the statement map. A structural/public checkout may omit those
    bytes, but only an already-validated immutable receipt with the exact same
    current map pin can authorize that absence. Present bytes are always read
    and compared, even on the structural path.
    """

    map_path = _paper_sidecar(folder, "paper_statement_map.json")
    statement_map = _load_object(map_path) if map_path is not None else None
    if statement_map is None:
        return (
            None,
            "",
            "statement map is unavailable for canonical-source verification",
        )
    raw_path = str(statement_map.get("source_artifact_path") or "").strip()
    expected = _sha256(statement_map.get("source_artifact_sha256"))
    pure_path = PurePosixPath(raw_path)
    if (
        not raw_path
        or pure_path.is_absolute()
        or ".." in pure_path.parts
        or not expected
    ):
        return None, "", "statement map canonical source pin is malformed"
    anchor = root if pure_path.parts[:1] == ("papers",) else folder
    try:
        artifact_path = (anchor / Path(*pure_path.parts)).resolve()
        artifact_path.relative_to(folder.resolve())
    except (OSError, RuntimeError, ValueError):
        return None, "", "statement map canonical source path escapes its paper folder"

    baseline: dict[str, object] | None = None
    if baseline_attestation is not None:
        try:
            baseline = _validated_canonical_source_attestation(baseline_attestation)
        except ValueError as exc:
            return None, "", str(exc)
        if (
            baseline["source_artifact_path"] != pure_path.as_posix()
            or baseline["expected_sha256"] != expected
        ):
            return (
                None,
                "",
                "current canonical source pin differs from immutable issuance",
            )

    if artifact_path.exists() and not artifact_path.is_file():
        return None, "", "canonical source artifact is not a regular file"
    if artifact_path.is_file():
        try:
            content = artifact_path.read_bytes()
        except OSError as exc:
            return None, "", f"canonical source artifact cannot be read: {exc}"
        observed = hashlib.sha256(content).hexdigest()
        if observed != expected:
            return (
                None,
                "",
                "canonical source artifact bytes disagree with the statement-map pin",
            )
        current = {
            "schema": CANONICAL_SOURCE_ATTESTATION_SCHEMA,
            "source_artifact_path": pure_path.as_posix(),
            "expected_sha256": expected,
            "observed_sha256": observed,
            "byte_length": len(content),
            "validator": CANONICAL_SOURCE_PIN_VALIDATOR_ID,
        }
        if baseline is not None and current != baseline:
            return (
                None,
                "",
                "current canonical source bytes differ from immutable issuance",
            )
        return current, "verified_current_bytes", ""

    if baseline is None:
        return (
            None,
            "",
            "canonical source bytes are required when issuing a reuse receipt",
        )
    return baseline, "structural_checkout_immutable_attestation", ""


def _validated_counts(value: object, *, keys: set[str], lane: str) -> dict[str, int]:
    if not isinstance(value, Mapping) or set(value) != keys:
        raise ValueError(f"saved {lane} counts are malformed")
    counts: dict[str, int] = {}
    for key in sorted(keys):
        raw = value.get(key)
        if not isinstance(raw, int) or isinstance(raw, bool) or raw < 0:
            raise ValueError(f"saved {lane} count {key} is invalid")
        counts[key] = raw
    if lane == "statement":
        if counts["total"] != sum(
            counts[key]
            for key in (
                "matches",
                "mismatch",
                "formalization_boundary",
                "uncertain",
                "unknown",
            )
        ):
            raise ValueError("saved statement counts do not partition statement rows")
    elif counts["total"] != sum(
        counts[key]
        for key in (
            "covered",
            "corrected_target_covered",
            "conditional_boundary",
            "support_only",
            "out_of_scope",
            "scope_exclusion",
        )
    ):
        raise ValueError("saved coverage counts do not partition selected source rows")
    return counts


def _validated_coverage_source_bindings(
    value: object,
) -> list[dict[str, str]]:
    if not isinstance(value, (list, tuple)) or not value:
        raise ValueError("saved coverage source bindings are malformed")
    bindings: list[dict[str, str]] = []
    raw_digests: set[str] = set()
    canonical_digests: set[str] = set()
    for raw in value:
        if not isinstance(raw, Mapping) or set(raw) != {
            "source_map_item_semantic_sha256",
            "source_item_semantic_sha256",
        }:
            raise ValueError("saved coverage source binding fields are malformed")
        raw_digest = _sha256(raw.get("source_map_item_semantic_sha256"))
        canonical_digest = _sha256(raw.get("source_item_semantic_sha256"))
        if (
            not raw_digest
            or not canonical_digest
            or raw_digest in raw_digests
            or canonical_digest in canonical_digests
        ):
            raise ValueError("saved coverage source bindings are not bijective")
        raw_digests.add(raw_digest)
        canonical_digests.add(canonical_digest)
        bindings.append(
            {
                "source_map_item_semantic_sha256": raw_digest,
                "source_item_semantic_sha256": canonical_digest,
            }
        )
    return sorted(bindings, key=stable_sha256)


def validated_coverage_source_bindings(
    value: object,
) -> tuple[Mapping[str, str], ...]:
    """Return a copied, canonical semantic source-binding tuple.

    Map keys and source/declaration names are deliberately absent.  Callers may
    use the raw-map semantic digest to locate one current map row, while the
    selected-item semantic digest remains the immutable coverage identity.
    """

    return tuple(
        dict(binding) for binding in _validated_coverage_source_bindings(value)
    )


def _load_object(path: Path) -> dict[str, Any] | None:
    try:
        value = json.loads(path.read_text(encoding="utf-8"))
    except (OSError, UnicodeError, json.JSONDecodeError):
        return None
    return value if isinstance(value, dict) else None


def _paper_sidecar(folder: Path, basename: str) -> Path | None:
    for path in (folder / "audit" / basename, folder / basename):
        if path.is_file():
            return path
    return None


def _metadata_complete(payload: Mapping[str, Any]) -> bool:
    validator = str(
        payload.get("validator")
        or payload.get("model")
        or payload.get("judge")
        or payload.get("agent")
        or payload.get("generator")
        or ""
    ).strip()
    validator_type = str(
        payload.get("validator_type") or payload.get("generator_type") or ""
    ).strip()
    validated_at = str(
        payload.get("validated_at")
        or payload.get("timestamp")
        or payload.get("generated_at")
        or ""
    ).strip()
    return bool(validator and validator_type and validated_at)


def _first_present(item: Mapping[str, Any], fields: tuple[str, ...]) -> object:
    for field in fields:
        if field in item and item[field] is not None:
            return item[field]
    return None


def _normalize_statement_judgment(value: object) -> str:
    if isinstance(value, bool):
        return "matches" if value else "mismatch"
    normalized = str(value or "").strip().lower().replace("-", "_")
    aliases = {
        "match": "matches",
        "yes": "matches",
        "true": "matches",
        "equivalent": "matches",
        "same": "matches",
        "does_not_match": "mismatch",
        "does not match": "mismatch",
        "no": "mismatch",
        "false": "mismatch",
        "different": "mismatch",
        "unsure": "uncertain",
        "partial": "uncertain",
        "needs_review": "uncertain",
    }
    return aliases.get(normalized, normalized)


def _normalize_coverage(value: object) -> str:
    if isinstance(value, bool):
        return "covered" if value else "missing"
    return str(value or "").strip().lower().replace("-", "_").replace(" ", "_")


def _statement_item_identity(
    raw_item: Mapping[str, Any],
) -> tuple[dict[str, str] | None, str]:
    lean = _sha256(raw_item.get("lean_signature_sha256"))
    paper = _sha256(raw_item.get("paper_statement_sha256"))
    tex = _sha256(raw_item.get("tex_statement_sha256"))
    if not lean or not paper or not tex:
        return None, "statement row lacks a complete semantic digest triple"
    judgment = _normalize_statement_judgment(
        _first_present(raw_item, ("judgment", "verdict", "status", "matches"))
    )
    if judgment not in {"matches", "mismatch", "uncertain", "unknown"}:
        return None, "statement row has an unsupported judgment"
    resolution = (
        str(
            raw_item.get("resolution")
            or raw_item.get("accepted_resolution")
            or raw_item.get("review_resolution")
            or ""
        )
        .strip()
        .lower()
    )
    if judgment == "mismatch" and resolution not in {"", "conditional_boundary"}:
        return None, "statement mismatch has an unsupported resolution"
    if judgment != "mismatch" and resolution not in {"", "approved_corrected_target"}:
        return None, "statement judgment has an incompatible resolution"
    if not str(
        raw_item.get("reason")
        or raw_item.get("notes")
        or raw_item.get("explanation")
        or ""
    ).strip():
        return None, "statement row lacks semantic review evidence"
    return {
        "lean_signature_sha256": lean,
        "paper_statement_sha256": paper,
        "tex_statement_sha256": tex,
        "judgment": judgment,
        "resolution": resolution,
    }, ""


def _configured_review_surface(
    folder: Path,
) -> tuple[tuple[str, ...] | None, tuple[str, ...] | None, str]:
    status = _load_object(folder / "status.json")
    review_surface = status.get("review_surface") if status is not None else None
    if not isinstance(review_surface, Mapping):
        return None, None, "status has no configured review surface"

    def navigation(field: str, *, required: bool) -> tuple[str, ...] | None:
        raw = review_surface.get(field)
        if raw is None and not required:
            return ()
        if not isinstance(raw, list):
            return None
        values = tuple(str(value).strip() for value in raw)
        if any(not value for value in values) or len(values) != len(set(values)):
            return None
        return values

    statements = navigation("include_names", required=True)
    assumptions = navigation("assumption_names", required=False)
    if statements is None or not statements:
        return None, None, "configured statement review surface is malformed or empty"
    if assumptions is None or set(statements).intersection(assumptions):
        return (
            None,
            None,
            "configured source-condition surface is malformed or ambiguous",
        )
    return statements, assumptions, ""


def _assumption_item_identity(
    raw_item: Mapping[str, Any],
) -> tuple[dict[str, str] | None, str]:
    lean = _sha256(raw_item.get("lean_statement_sha256"))
    paper = _sha256(raw_item.get("paper_statement_sha256"))
    judgment = str(raw_item.get("judgment") or "").strip().lower().replace("-", "_")
    approved = {
        "documented_additional_assumption",
        "paper_assumption",
        "paper_condition",
        "partial_boundary",
        "source_text_model_primitive",
    }
    if not lean or not paper:
        return None, "source-condition row lacks complete semantic digests"
    if judgment not in approved:
        return None, "source-condition row has an unsupported judgment"
    if not str(raw_item.get("reason") or "").strip():
        return None, "source-condition row lacks semantic review evidence"
    return {
        "lean_statement_sha256": lean,
        "paper_statement_sha256": paper,
        "judgment": judgment,
    }, ""


def _selected_semantic_rows(
    *,
    raw_items: Mapping[str, Any],
    navigation: tuple[str, ...],
    identity_builder: Any,
    lane: str,
) -> tuple[list[dict[str, str]] | None, str]:
    """Resolve navigation labels once, then retain only semantic identities."""

    selected: list[dict[str, str]] = []
    target_identities: set[str] = set()
    for locator in navigation:
        raw_item = raw_items.get(locator)
        if not isinstance(raw_item, Mapping):
            return None, f"configured {lane} row has no current sidecar item"
        identity, error = identity_builder(raw_item)
        if identity is None:
            return None, error
        target = stable_sha256(
            {
                f"{lane}_semantic_target": {
                    key: value
                    for key, value in identity.items()
                    if key not in {"judgment", "resolution"}
                }
            }
        )
        if target in target_identities:
            return None, f"configured {lane} rows do not resolve uniquely by semantics"
        target_identities.add(target)
        selected.append(identity)
    return selected, ""


def statement_disposition(
    folder: Path,
) -> tuple[SavedStatusDisposition | None, SavedStatusReuseProblem | None]:
    path = _paper_sidecar(folder, "statement_match_llm.json")
    payload = _load_object(path) if path is not None else None
    if payload is None:
        return None, SavedStatusReuseProblem("statement", "sidecar is unavailable")
    raw_items = payload.get("items")
    if (
        payload.get("schema") != 1
        or payload.get("paper") not in {None, folder.name}
        or not isinstance(raw_items, dict)
        or not raw_items
        or not _metadata_complete(payload)
    ):
        return None, SavedStatusReuseProblem(
            "statement", "sidecar schema, paper, metadata, or items are malformed"
        )
    statement_navigation, assumption_navigation, surface_error = (
        _configured_review_surface(folder)
    )
    if statement_navigation is None or assumption_navigation is None:
        return None, SavedStatusReuseProblem("statement", surface_error)
    identities, selection_error = _selected_semantic_rows(
        raw_items=raw_items,
        navigation=statement_navigation,
        identity_builder=_statement_item_identity,
        lane="statement",
    )
    if identities is None:
        return None, SavedStatusReuseProblem("statement", selection_error)
    counts = {
        "total": 0,
        "matches": 0,
        "mismatch": 0,
        "formalization_boundary": 0,
        "uncertain": 0,
        "unknown": 0,
        "source_condition_rows": 0,
    }
    for identity in identities:
        counts["total"] += 1
        judgment = identity["judgment"]
        if judgment == "matches":
            counts["matches"] += 1
        elif (
            judgment == "mismatch" and identity["resolution"] == "conditional_boundary"
        ):
            counts["formalization_boundary"] += 1
        else:
            counts[judgment] += 1

    source_conditions: list[dict[str, str]] = []
    assumption_prompt_version = ""
    if assumption_navigation:
        assumption_path = _paper_sidecar(folder, "assumption_match_llm.json")
        assumption_payload = (
            _load_object(assumption_path) if assumption_path is not None else None
        )
        assumption_items = (
            assumption_payload.get("items")
            if isinstance(assumption_payload, Mapping)
            else None
        )
        if (
            not isinstance(assumption_payload, Mapping)
            or assumption_payload.get("schema") != 1
            or assumption_payload.get("paper") not in {None, folder.name}
            or not isinstance(assumption_items, Mapping)
            or not _metadata_complete(assumption_payload)
        ):
            return None, SavedStatusReuseProblem(
                "statement", "configured source-condition sidecar is unavailable"
            )
        selected_conditions, condition_error = _selected_semantic_rows(
            raw_items=assumption_items,
            navigation=assumption_navigation,
            identity_builder=_assumption_item_identity,
            lane="source_condition",
        )
        if selected_conditions is None:
            return None, SavedStatusReuseProblem("statement", condition_error)
        source_conditions = selected_conditions
        counts["source_condition_rows"] = len(source_conditions)
        assumption_prompt_version = str(
            assumption_payload.get("prompt_version") or ""
        ).strip()
    projection = {
        "schema": STATEMENT_DISPOSITION_SCHEMA,
        "prompt_version": str(payload.get("prompt_version") or "").strip(),
        "items": sorted(identities, key=stable_sha256),
        "source_condition_prompt_version": assumption_prompt_version,
        "source_conditions": sorted(source_conditions, key=stable_sha256),
    }
    return (
        SavedStatusDisposition(
            stable_sha256(projection),
            counts,
        ),
        None,
    )


def _configured_review_semantic_index(
    folder: Path,
) -> tuple[dict[str, str] | None, SavedStatusReuseProblem | None]:
    path = _paper_sidecar(folder, "statement_match_llm.json")
    payload = _load_object(path) if path is not None else None
    raw_items = payload.get("items") if isinstance(payload, dict) else None
    if not isinstance(raw_items, dict) or not raw_items:
        return None, SavedStatusReuseProblem(
            "coverage", "statement semantic index is unavailable"
        )
    statement_navigation, assumption_navigation, surface_error = (
        _configured_review_surface(folder)
    )
    if statement_navigation is None or assumption_navigation is None:
        return None, SavedStatusReuseProblem("coverage", surface_error)
    index: dict[str, str] = {}
    semantic_targets: set[str] = set()
    for key in statement_navigation:
        raw_item = raw_items.get(key)
        if not isinstance(raw_item, dict):
            return None, SavedStatusReuseProblem(
                "coverage", "configured review target has no current semantic row"
            )
        identity, error = _statement_item_identity(raw_item)
        if identity is None:
            return None, SavedStatusReuseProblem("coverage", error)
        semantic_target = stable_sha256(
            {
                "statement_semantic_target": {
                    "lean_signature_sha256": identity["lean_signature_sha256"],
                    "paper_statement_sha256": identity["paper_statement_sha256"],
                    "tex_statement_sha256": identity["tex_statement_sha256"],
                }
            }
        )
        if semantic_target in semantic_targets:
            return None, SavedStatusReuseProblem(
                "coverage", "configured review targets are semantically ambiguous"
            )
        semantic_targets.add(semantic_target)
        index[key] = semantic_target
    if assumption_navigation:
        assumption_path = _paper_sidecar(folder, "assumption_match_llm.json")
        assumption_payload = (
            _load_object(assumption_path) if assumption_path is not None else None
        )
        assumption_items = (
            assumption_payload.get("items")
            if isinstance(assumption_payload, Mapping)
            else None
        )
        if (
            not isinstance(assumption_payload, Mapping)
            or assumption_payload.get("schema") != 1
            or assumption_payload.get("paper") not in {None, folder.name}
            or not isinstance(assumption_items, Mapping)
            or not _metadata_complete(assumption_payload)
        ):
            return None, SavedStatusReuseProblem(
                "coverage", "configured source-condition target index is unavailable"
            )
        for key in assumption_navigation:
            raw_item = assumption_items.get(key)
            if not isinstance(raw_item, Mapping):
                return None, SavedStatusReuseProblem(
                    "coverage",
                    "configured source-condition target has no current semantic row",
                )
            identity, error = _assumption_item_identity(raw_item)
            if identity is None:
                return None, SavedStatusReuseProblem("coverage", error)
            semantic_target = stable_sha256(
                {
                    "source_condition_semantic_target": {
                        "lean_statement_sha256": identity["lean_statement_sha256"],
                        "paper_statement_sha256": identity["paper_statement_sha256"],
                    }
                }
            )
            if semantic_target in semantic_targets:
                return None, SavedStatusReuseProblem(
                    "coverage", "configured review targets are semantically ambiguous"
                )
            semantic_targets.add(semantic_target)
            index[key] = semantic_target
    return index, None


def _resolved_target_identities(
    raw: object,
    statement_index: Mapping[str, str],
    *,
    lane: str,
) -> tuple[list[str] | None, str]:
    if raw is None:
        values: list[object] = []
    elif isinstance(raw, list):
        values = raw
    else:
        return None, f"{lane} targets are not a list"
    if len(values) != len({str(value).strip() for value in values}):
        return None, f"{lane} targets contain duplicates"
    resolved: list[str] = []
    for raw_value in values:
        value = str(raw_value).strip()
        identity = statement_index.get(value)
        if not value or not identity:
            return None, f"{lane} target has no unique configured semantic identity"
        resolved.append(identity)
    return sorted(resolved), ""


def _canonical_coverage_source_bindings(
    folder: Path,
    statement_map: Mapping[str, Any],
    coverage: Mapping[str, Any],
    mode: str,
) -> tuple[list[dict[str, str]] | None, bool, str]:
    """Extract the dashboard's exact selected source set only for reissue."""

    try:
        import review_dashboard
    except ModuleNotFoundError:  # pragma: no cover - module-style imports.
        from scripts import review_dashboard
    try:
        full_inventory, selected_inventory, selected_mode, mode_error = (
            review_dashboard.paper_coverage_inventory(folder)
        )
    except Exception as exc:
        return (
            None,
            False,
            f"canonical selected source surface is unavailable: {exc}",
        )
    if mode_error or selected_mode != mode:
        return None, False, mode_error or "canonical source coverage mode changed"
    if not selected_inventory:
        return None, False, "canonical selected source surface is empty"
    map_items = statement_map.get("items")
    if not isinstance(map_items, Mapping):
        return None, False, "statement map has no source items"
    bindings: list[dict[str, str]] = []
    for key, canonical_item in selected_inventory.items():
        raw_item = map_items.get(key)
        if not isinstance(raw_item, dict):
            return (
                None,
                False,
                "canonical source selection has no raw semantic item",
            )
        bindings.append(
            {
                "source_map_item_semantic_sha256": source_item_coverage_sha256(
                    raw_item, mode
                ),
                "source_item_semantic_sha256": source_item_coverage_sha256(
                    canonical_item, mode
                ),
            }
        )
    try:
        validated = _validated_coverage_source_bindings(bindings)
    except ValueError as exc:
        return None, False, str(exc)
    recorded_inventory = (
        str(
            coverage.get("paper_statement_inventory_sha256")
            or coverage.get("statement_inventory_sha256")
            or coverage.get("inventory_sha256")
            or ""
        )
        .strip()
        .lower()
    )
    current_inventory_digests = {
        review_dashboard.paper_coverage_inventory_digest(
            selected_inventory,
            mode=mode,
            statement_map_payload=dict(statement_map),
        ),
        review_dashboard.paper_statement_inventory_digest(full_inventory),
    }
    return validated, recorded_inventory in current_inventory_digests, ""


def coverage_disposition(
    folder: Path,
    *,
    source_bindings: object | None = None,
) -> tuple[SavedStatusDisposition | None, SavedStatusReuseProblem | None]:
    coverage_path = _paper_sidecar(folder, "paper_coverage_llm.json")
    map_path = _paper_sidecar(folder, "paper_statement_map.json")
    coverage = _load_object(coverage_path) if coverage_path is not None else None
    statement_map = _load_object(map_path) if map_path is not None else None
    if coverage is None or statement_map is None:
        return None, SavedStatusReuseProblem(
            "coverage", "coverage sidecar or statement map is unavailable"
        )
    raw_items = coverage.get("items")
    map_items = statement_map.get("items")
    audit_kind = str(
        coverage.get("audit_kind")
        or coverage.get("coverage_audit_kind")
        or coverage.get("kind")
        or ""
    ).strip()
    if (
        coverage.get("schema") != 1
        or coverage.get("paper") not in {None, folder.name}
        or not isinstance(raw_items, dict)
        or not raw_items
        or coverage.get("source_grounded") is not True
        or coverage.get("seed_scaffold") is True
        or audit_kind not in APPROVED_COVERAGE_AUDIT_KINDS
        or not _metadata_complete(coverage)
        or not isinstance(map_items, dict)
        or not map_items
    ):
        return None, SavedStatusReuseProblem(
            "coverage", "sidecar schema, provenance, metadata, or items are malformed"
        )
    mode, mode_error = source_coverage_mode_from_map(statement_map)
    if mode_error:
        return None, SavedStatusReuseProblem("coverage", mode_error)
    if source_bindings is None:
        bindings, legacy_aggregate_current, binding_error = (
            _canonical_coverage_source_bindings(
                folder,
                statement_map,
                coverage,
                mode,
            )
        )
        if bindings is None:
            return None, SavedStatusReuseProblem("coverage", binding_error)
    else:
        try:
            bindings = _validated_coverage_source_bindings(source_bindings)
        except ValueError as exc:
            return None, SavedStatusReuseProblem("coverage", str(exc))
        # The immutable receipt was issued only after the legacy aggregate was
        # current. Rehashing its saved raw-map binding makes that decision
        # portable without rerunning source-index extraction during status sync.
        legacy_aggregate_current = True
    map_keys_by_raw_digest: dict[str, list[str]] = {}
    for raw_key, raw_item in map_items.items():
        key = str(raw_key).strip()
        if not key or not isinstance(raw_item, dict):
            continue
        raw_digest = source_item_coverage_sha256(raw_item, mode)
        if _sha256(raw_digest):
            map_keys_by_raw_digest.setdefault(raw_digest, []).append(key)
    source_identities: dict[str, str] = {}
    for binding in bindings:
        raw_digest = binding["source_map_item_semantic_sha256"]
        matching_keys = map_keys_by_raw_digest.get(raw_digest, [])
        if len(matching_keys) != 1:
            return None, SavedStatusReuseProblem(
                "coverage",
                "saved selected source identity has no unique current map item",
            )
        source_identities[matching_keys[0]] = binding["source_item_semantic_sha256"]
    source_identity_set = set(source_identities.values())
    review_target_index, target_problem = _configured_review_semantic_index(folder)
    if review_target_index is None:
        return None, target_problem

    legacy_selected_inventory: Mapping[str, Mapping[str, Any]] = {}
    if any(
        isinstance(item, Mapping)
        and item.get("source_item_coverage_digest_schema")
        == SOURCE_ITEM_COVERAGE_DIGEST_SCHEMA
        for item in raw_items.values()
    ):
        try:
            import review_dashboard
        except ModuleNotFoundError:  # pragma: no cover - module-style imports.
            from scripts import review_dashboard
        try:
            _full, selected, selected_mode, selection_error = (
                review_dashboard.paper_coverage_inventory(folder)
            )
        except Exception as exc:
            return None, SavedStatusReuseProblem(
                "coverage",
                f"canonical selected source surface is unavailable: {exc}",
            )
        if selection_error or selected_mode != mode:
            return None, SavedStatusReuseProblem(
                "coverage",
                selection_error or "canonical source coverage mode changed",
            )
        legacy_selected_inventory = selected

    projections: list[dict[str, object]] = []
    counts = {
        "total": 0,
        "covered": 0,
        "corrected_target_covered": 0,
        "conditional_boundary": 0,
        "support_only": 0,
        "out_of_scope": 0,
        "scope_exclusion": 0,
    }
    selected_rows: dict[str, Mapping[str, Any]] = {}
    for raw_key, raw_item in raw_items.items():
        key = str(raw_key).strip()
        if not key:
            return None, SavedStatusReuseProblem(
                "coverage", "sidecar contains a malformed coverage row"
            )
        keyed_identity = source_identities.get(key, "")
        if not isinstance(raw_item, dict):
            if keyed_identity:
                return None, SavedStatusReuseProblem(
                    "coverage", "selected coverage row is malformed"
                )
            continue
        raw_recorded_identity = raw_item.get("source_item_coverage_sha256")
        recorded_source_identity = _sha256(raw_recorded_identity)
        digest_schema = raw_item.get("source_item_coverage_digest_schema")
        current_digest_schema = digest_schema == SOURCE_ITEM_COVERAGE_DIGEST_SCHEMA
        if raw_recorded_identity is not None and not recorded_source_identity:
            if keyed_identity:
                return None, SavedStatusReuseProblem(
                    "coverage", "selected coverage row has a malformed source digest"
                )
            continue
        if (
            keyed_identity
            and current_digest_schema
            and not recorded_source_identity
        ):
            return None, SavedStatusReuseProblem(
                "coverage", "selected coverage row lacks its current source digest"
            )
        if keyed_identity and current_digest_schema:
            selected_item = legacy_selected_inventory.get(key)
            if not isinstance(selected_item, dict) or not source_item_coverage_receipt_matches(
                selected_item,
                mode,
                digest_schema=digest_schema,
                digest=recorded_source_identity,
                legacy_navigation_key=key,
            ):
                return None, SavedStatusReuseProblem(
                    "coverage",
                    "selected coverage row source digest disagrees with the current map",
                )
            source_identity = keyed_identity
        elif keyed_identity:
            if not legacy_aggregate_current:
                return None, SavedStatusReuseProblem(
                    "coverage",
                    "selected legacy coverage row has no current aggregate source identity",
                )
            source_identity = keyed_identity
        elif current_digest_schema:
            source_identity = recorded_source_identity
        else:
            # A legacy digest has a different semantic schema and cannot bind a
            # renamed row by itself. Exact-key binding remains available only
            # under the current aggregate or an already-issued receipt.
            source_identity = ""
        if source_identity not in source_identity_set:
            # Surplus deep-audit coverage rows remain diagnostics and do not
            # alter normal named-theory status counts or receipt identity.
            continue
        if source_identity in selected_rows:
            return None, SavedStatusReuseProblem(
                "coverage", "multiple coverage rows bind one selected source identity"
            )
        selected_rows[source_identity] = raw_item

    if set(selected_rows) != source_identity_set:
        return None, SavedStatusReuseProblem(
            "coverage",
            "coverage sidecar is not a bijection over the selected source surface",
        )

    for source_identity in sorted(selected_rows):
        raw_item = selected_rows[source_identity]
        judgment = _normalize_coverage(
            _first_present(
                raw_item,
                ("coverage", "judgment", "verdict", "status", "covered"),
            )
        )
        if judgment not in (
            DIRECT_COVERAGE
            | BOUNDARY_COVERAGE
            | SUPPORT_COVERAGE
            | OUT_OF_SCOPE_COVERAGE
            | {CORRECTED_COVERAGE}
        ):
            return None, SavedStatusReuseProblem(
                "coverage", "coverage row has no approved terminal disposition"
            )
        if (
            not str(
                raw_item.get("reason")
                or raw_item.get("notes")
                or raw_item.get("explanation")
                or ""
            ).strip()
            or not str(raw_item.get("source_evidence") or "").strip()
        ):
            return None, SavedStatusReuseProblem(
                "coverage", "coverage row lacks source-grounded semantic evidence"
            )
        review_targets, target_error = _resolved_target_identities(
            raw_item.get("review_rows"),
            review_target_index,
            lane="review-row",
        )
        if review_targets is None:
            return None, SavedStatusReuseProblem("coverage", target_error)
        support_targets: list[str] = []
        if judgment in SUPPORT_COVERAGE:
            resolved_support, support_error = _resolved_target_identities(
                raw_item.get("support_declarations"),
                review_target_index,
                lane="support",
            )
            if resolved_support is None:
                return None, SavedStatusReuseProblem("coverage", support_error)
            support_targets = resolved_support
        if judgment in DIRECT_COVERAGE | BOUNDARY_COVERAGE | {CORRECTED_COVERAGE}:
            if not review_targets:
                return None, SavedStatusReuseProblem(
                    "coverage", "direct coverage row has no semantic review target"
                )
        elif judgment in SUPPORT_COVERAGE:
            if not support_targets:
                return None, SavedStatusReuseProblem(
                    "coverage", "support-only row has no semantic support target"
                )
        elif review_targets or support_targets:
            return None, SavedStatusReuseProblem(
                "coverage", "scoped-out row unexpectedly claims a Lean target"
            )
        projections.append(
            {
                "source_item_semantic_sha256": source_identity,
                "coverage": judgment,
                "review_target_semantic_sha256s": review_targets,
                "support_target_semantic_sha256s": support_targets,
            }
        )
        counts["total"] += 1
        if judgment in DIRECT_COVERAGE:
            counts["covered"] += 1
        elif judgment == CORRECTED_COVERAGE:
            counts["corrected_target_covered"] += 1
        elif judgment in BOUNDARY_COVERAGE:
            counts["conditional_boundary"] += 1
        elif judgment in SUPPORT_COVERAGE:
            counts["support_only"] += 1
        elif judgment == "user_approved_scope_exclusion":
            counts["scope_exclusion"] += 1
        else:
            counts["out_of_scope"] += 1
    projection = {
        "schema": COVERAGE_DISPOSITION_SCHEMA,
        "audit_kind": audit_kind,
        "prompt_version": str(coverage.get("prompt_version") or "").strip(),
        "source_coverage_mode": mode,
        "items": sorted(projections, key=stable_sha256),
    }
    return (
        SavedStatusDisposition(
            stable_sha256(projection),
            counts,
            tuple(bindings),
        ),
        None,
    )


def current_saved_status_reuse_receipt(
    root: Path,
    folder: Path,
    *,
    closure_provider: WorktreeImportClosureProvider | None = None,
    baseline_lean_closure: object | None = None,
    baseline_coverage_source_bindings: object | None = None,
    baseline_canonical_source_attestation: object | None = None,
) -> tuple[SavedStatusReuseReceipt | None, SavedStatusReuseProblem | None]:
    root = root.resolve()
    folder = folder.resolve()
    try:
        relative = folder.relative_to(root / "papers")
    except ValueError:
        return None, SavedStatusReuseProblem(
            "closure", "paper folder is outside the repository papers tree"
        )
    if len(relative.parts) != 1:
        return None, SavedStatusReuseProblem(
            "closure", "paper folder is not one direct paper directory"
        )
    source_attestation, source_state, source_error = (
        _current_canonical_source_attestation(
            root,
            folder,
            baseline_attestation=baseline_canonical_source_attestation,
        )
    )
    if source_attestation is None:
        return None, SavedStatusReuseProblem("source", source_error)
    entrypoint = f"papers/{relative.name}/PaperInterface.lean"
    try:
        provider = closure_provider or WorktreeImportClosureProvider(root)
        if baseline_lean_closure is None:
            closure_record, closure_problem = provider.record_for_entrypoint(entrypoint)
            closure_sha256 = (
                lean_import_closure_payload_sha256(closure_record)
                if closure_record is not None
                else None
            )
        else:
            closure_record = validated_lean_import_closure_payload(
                baseline_lean_closure
            )
            closure_sha256, closure_problem = provider.identity_from_saved_closure(
                entrypoint,
                closure_record,
            )
    except Exception as exc:
        return None, SavedStatusReuseProblem(
            "closure", f"Lean import-closure provider is unavailable: {exc}"
        )
    if closure_sha256 is None:
        reason = (
            closure_problem.format()
            if closure_problem is not None
            else "Lean import closure identity is unavailable"
        )
        return None, SavedStatusReuseProblem("closure", reason)
    statement, statement_problem = statement_disposition(folder)
    if statement is None:
        return None, statement_problem
    coverage, coverage_problem = coverage_disposition(
        folder,
        source_bindings=baseline_coverage_source_bindings,
    )
    if coverage is None:
        return None, coverage_problem
    return (
        SavedStatusReuseReceipt(
            lean_candidate_closure=closure_record,
            lean_candidate_closure_sha256=closure_sha256,
            statement_disposition_sha256=statement.sha256,
            coverage_disposition_sha256=coverage.sha256,
            canonical_source_attestation=source_attestation,
            coverage_source_bindings=tuple(
                dict(binding) for binding in coverage.source_bindings
            ),
            statement_counts=statement.counts,
            coverage_counts=coverage.counts,
            canonical_source_state=source_state,
        ),
        None,
    )
