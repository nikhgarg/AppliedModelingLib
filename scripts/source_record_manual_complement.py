#!/usr/bin/env python3
"""Prepare and materialize the current manual complement of v10 overlays.

An authenticated source-record overlay is intentionally narrow: it can supply
only the current groups whose complete semantic descriptors it replays.  This
tool makes the remaining work explicit without regenerating the raw audit.  A
template is a non-evidence review aid; a completed template becomes an
ordinary current sidecar only after it is bound again to every current raw
group and current item receipt.

Historical keys may occur in archived artifacts, but this tool never uses a
key, declaration name, binder name, or function name to infer a current
match.  The only reuse inputs are the existing authenticated overlay loaders.
The manual complement is calculated from the complete current raw-group
ledger, including groups not listed in an expected-key summary.
"""

from __future__ import annotations

import argparse
import copy
import hashlib
import json
import os
import sys
import tempfile
from dataclasses import dataclass
from pathlib import Path, PurePosixPath
from typing import Any, Mapping, Sequence


ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

try:  # Supports direct execution and package imports in focused tests.
    from scripts import source_record_current_revalidation as CURRENT
    from scripts import source_record_obligation_groups as OBLIGATIONS
    from scripts.source_record_integrity import canonical_digest_payload
    from scripts.formalization_protocol import (
        FORMALIZATION_REVIEW_PROTOCOL_FIELD,
        formalization_review_protocol_digest,
    )
    from scripts.source_record_record_closure_completion import (
        RECORD_FIELD_CLOSURE_COMPLETION_ATTESTATIONS_FIELD,
        RECORD_FIELD_CLOSURE_COMPLETION_RECEIPT_FIELD,
        RECORD_FIELD_CLOSURE_COMPLETION_RECEIPT_SCHEMA,
        RecordFieldClosureCompletionCandidate,
        closure_attestation_error,
        closure_attestation_for_candidate,
        closure_attestation_sha256,
        closure_completion_receipt_error,
        current_record_field_closure_completion_candidates,
    )
    from scripts.configured_assumption_formalization_regularities import (
        load_configured_assumption_formalization_regularity_context,
    )
    from scripts.source_record_target_disposition import (
        RECURSIVE_FIELD_EXPLICIT_PARENT_ROUTE_FIELD,
        project_source_record_response_association_pins,
    )
except ModuleNotFoundError:  # pragma: no cover - direct script fallback.
    import source_record_current_revalidation as CURRENT
    import source_record_obligation_groups as OBLIGATIONS
    from source_record_integrity import canonical_digest_payload
    from formalization_protocol import (
        FORMALIZATION_REVIEW_PROTOCOL_FIELD,
        formalization_review_protocol_digest,
    )
    from source_record_record_closure_completion import (
        RECORD_FIELD_CLOSURE_COMPLETION_ATTESTATIONS_FIELD,
        RECORD_FIELD_CLOSURE_COMPLETION_RECEIPT_FIELD,
        RECORD_FIELD_CLOSURE_COMPLETION_RECEIPT_SCHEMA,
        RecordFieldClosureCompletionCandidate,
        closure_attestation_error,
        closure_attestation_for_candidate,
        closure_attestation_sha256,
        closure_completion_receipt_error,
        current_record_field_closure_completion_candidates,
    )
    from configured_assumption_formalization_regularities import (
        load_configured_assumption_formalization_regularity_context,
    )
    from source_record_target_disposition import (
        RECURSIVE_FIELD_EXPLICIT_PARENT_ROUTE_FIELD,
        project_source_record_response_association_pins,
    )


SOURCE_RECORD_MANUAL_COMPLEMENT_SCHEMA = 1
SOURCE_RECORD_MANUAL_COMPLEMENT_POLICY_VERSION = (
    "source-record-v10-manual-current-complement-v3"
)
_LEGACY_SOURCE_RECORD_MANUAL_COMPLEMENT_POLICY_VERSION = (
    "source-record-v10-manual-current-complement-v2"
)
SOURCE_RECORD_MANUAL_COMPLEMENT_TEMPLATE_KIND = (
    "source_record_v10_manual_current_complement_template"
)
SOURCE_RECORD_MANUAL_COMPLEMENT_SCOPE = (
    "all_current_generated_groups_without_authenticated_overlay"
)
STRICT_V11_FULL_SPEC_RUNTIME_COVERAGE_FIELD = (
    "strict_v11_full_spec_runtime_covered_current_keys"
)
SOURCE_RECORD_MANUAL_COMPLEMENT_REVIEW_SEED_SCHEMA = 1
SOURCE_RECORD_MANUAL_COMPLEMENT_REVIEW_SEED_POLICY_VERSION = (
    "source-record-v10-manual-current-complement-review-seed-v1"
)
SOURCE_RECORD_MANUAL_COMPLEMENT_REVIEW_SEED_MATCH_RELATION = (
    "exact_canonical_group_descriptor_and_ordered_current_item_pins"
)
SOURCE_RECORD_MANUAL_COMPLEMENT_REVIEW_FRAGMENT_SCHEMA = 1
SOURCE_RECORD_MANUAL_COMPLEMENT_REVIEW_FRAGMENT_KIND = (
    "source_record_v10_manual_current_review_fragment"
)
_SHA256_HEX_LENGTH = 64
_RESPONSE_TRANSPORT_FIELDS = frozenset(
    {
        "prompt_version",
        "validator",
        "validated_at",
        "timestamp",
        "generated_at",
        "source_record_audit_sha256",
        "source_record_schema4_to5_migration",
        "source_record_differential_revalidation",
        "source_record_attested_selected_semantic_reuse",
        "source_record_historical_descriptor_migration",
        "source_record_scoped_receipt_rebind",
        "current_selected_semantic_revalidation_item",
        "prior_source_record_item_receipt",
        "authenticated_evidence_composition_item",
        "semantic_association_rebind",
        RECORD_FIELD_CLOSURE_COMPLETION_RECEIPT_FIELD,
    }
)

# A completed-template crosswalk deliberately transfers only reviewer-authored
# content.  The materializer below reconstructs these fields from the fresh
# raw audit, so retaining a historical copy would turn a template refresh into
# an unreviewed provenance bridge.  Keep this list explicit rather than
# dropping every ``*_sha256`` field: for example a model-convention digest can
# be part of the reviewed source-convention claim and is rechecked by the
# normal evidence gate.
_REBIND_RESPONSE_GENERATED_FIELDS = frozenset(
    {
        "schema",
        "artifact_kind",
        "policy_version",
        "paper",
        "current_source_record_audit_sha256",
        "generated_judgment_keys_sha256",
        "generated_judgment_surface_sha256",
        "authenticated_overlay_current_keys",
        "current_group_semantic_descriptor",
        "current_group_semantic_descriptor_sha256",
        "current_item_pins",
        "semantic_association_sha256",
        "source_contract_association_sha256",
        "source_map_item_keys",
        "source_map_item_keys_sha256",
        "source_map_item_sha256_by_key",
        "source_item_semantic_sha256",
        "source_item_semantic_sha256_by_key",
        "corrected_target_sha256",
        "corrected_target_sha256_by_source_item",
        "corrected_target_sha256_by_source_semantic_sha256",
        "source_target_disposition_sha256",
        "source_target_match_verdict",
        "configured_assumption_formalization_regularity_id",
        "configured_assumption_formalization_regularity_context_sha256",
        "source_contract_association",
        "semantic_contract_source_association",
        "source_statement_association",
        "statement_source_component_association",
        "semantic_contract_group",
        "recursive_field_explicit_parent_route",
        RECORD_FIELD_CLOSURE_COMPLETION_RECEIPT_FIELD,
        "source_record_audit_surface",
        "source_record_audit_integrity_sha256",
    }
    | _RESPONSE_TRANSPORT_FIELDS
)
_REBIND_RESPONSE_GENERATED_PREFIXES = (
    "source_record_",
    "raw_",
    "generated_",
)
_TEMPLATE_HUMAN_FIELDS = (
    "reviewed_current_semantics",
    "reviewer",
    "validated_at",
    "review_notes",
)
_TEMPLATE_CANDIDATE_MARKERS = frozenset(
    {
        "candidate_only",
        "is_candidate",
        "draft",
        "is_draft",
        "draft_only",
        "proposal_only",
        "not_evidence",
    }
)
_TEMPLATE_DRAFT_TEXT_FIELDS = frozenset(
    {
        "artifact_kind",
        "validator_type",
        "status",
        "review_status",
        "state",
    }
)


_NON_EVIDENCE_MARKERS = (
    "candidate_only",
    "not_evidence",
    "must_not_be_written_to_repository_sidecar",
    "non_evidence_scaffold",
)


class SourceRecordManualComplementError(ValueError):
    """Raised when current manual-complement evidence is incomplete or stale."""


class _ManualComplementWriteBoundaryDeferral:
    """Private capability allowing the CLI to defer one final check to its write."""

    __slots__ = ()


_MANUAL_COMPLEMENT_WRITE_BOUNDARY_DEFERRAL = _ManualComplementWriteBoundaryDeferral()


def _canonical_digest(payload: object) -> str:
    encoded = json.dumps(
        canonical_digest_payload(payload), sort_keys=True, separators=(",", ":")
    ).encode("utf-8")
    return hashlib.sha256(encoded).hexdigest()


def _sha256(value: object) -> str:
    text = str(value or "").strip().lower()
    if len(text) != _SHA256_HEX_LENGTH:
        return ""
    try:
        int(text, 16)
    except ValueError:
        return ""
    return text


def _read_json_object(path: Path) -> dict[str, Any]:
    try:
        payload = json.loads(path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError) as exc:
        raise SourceRecordManualComplementError(
            f"could not read JSON object at {path}: {exc}"
        ) from exc
    if not isinstance(payload, dict):
        raise SourceRecordManualComplementError(f"{path} is not a JSON object")
    return payload


def _paper_path(path: Path, paper_dir: Path, *, label: str) -> Path:
    try:
        resolved = path.resolve()
        resolved.relative_to(paper_dir.resolve())
    except (OSError, RuntimeError, ValueError) as exc:
        raise SourceRecordManualComplementError(
            f"{label} must remain inside {paper_dir}"
        ) from exc
    return resolved


def _relative_paper_path(path: Path, paper_dir: Path) -> str:
    try:
        return path.resolve().relative_to(paper_dir.resolve()).as_posix()
    except (OSError, RuntimeError, ValueError) as exc:
        raise SourceRecordManualComplementError(
            f"{path} must remain inside {paper_dir}"
        ) from exc


def _normalized_relative_paper_path(value: object, paper_dir: Path, *, label: str) -> Path:
    text = str(value or "").strip()
    pure = PurePosixPath(text)
    if (
        not text
        or pure.is_absolute()
        or any(part in {"", ".", ".."} for part in pure.parts)
    ):
        raise SourceRecordManualComplementError(
            f"{label} must be a normalized paper-relative path"
        )
    path = (paper_dir / Path(*pure.parts)).resolve()
    if _relative_paper_path(path, paper_dir) != text:
        raise SourceRecordManualComplementError(f"{label} is not canonical")
    return path


def _atomic_write(path: Path, contents: str) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    with tempfile.NamedTemporaryFile(
        dir=path.parent,
        prefix=f".{path.name}.",
        delete=False,
        mode="w",
        encoding="utf-8",
    ) as handle:
        handle.write(contents)
        temporary = Path(handle.name)
    try:
        os.replace(temporary, path)
    finally:
        if temporary.exists():
            temporary.unlink()


def _raw_groups(
    raw_audit: Mapping[str, Any], *, paper: str, paper_dir: Path | None = None
) -> dict[str, dict[str, Any]]:
    """Return complete current groups, rejecting a malformed/raw stale surface."""

    if error := CURRENT._raw_audit_error(
        raw_audit, paper=paper, paper_dir=paper_dir
    ):
        raise SourceRecordManualComplementError(error)
    groups, group_errors = OBLIGATIONS.raw_source_record_obligation_groups(raw_audit)
    if group_errors:
        raise SourceRecordManualComplementError(
            "current raw audit has malformed semantic groups: "
            + ", ".join(sorted(group_errors)[:5])
        )
    generated = CURRENT.generated_judgment_items(raw_audit)
    if set(groups) != set(generated):
        missing = sorted(set(generated) - set(groups))
        extra = sorted(set(groups) - set(generated))
        raise SourceRecordManualComplementError(
            "current raw semantic-group ledger disagrees with reusable-group ledger"
            + (f"; missing={missing[:5]}" if missing else "")
            + (f"; extra={extra[:5]}" if extra else "")
        )
    out: dict[str, dict[str, Any]] = {}
    for key, raw_group in groups.items():
        descriptor = raw_group.get("descriptor")
        descriptor_sha256 = _sha256(raw_group.get("descriptor_sha256"))
        raw_members = raw_group.get("raw_members")
        if (
            not isinstance(descriptor, Mapping)
            or not descriptor_sha256
            or _canonical_digest(descriptor) != descriptor_sha256
            or not isinstance(raw_members, list)
        ):
            raise SourceRecordManualComplementError(
                f"current raw group `{key}` has malformed descriptor or members"
            )
        try:
            pins = CURRENT._current_item_pins(raw_members)
        except CURRENT.SourceRecordCurrentRevalidationError as exc:
            raise SourceRecordManualComplementError(
                f"current raw group `{key}` has malformed item pins: {exc}"
            ) from exc
        out[key] = {
            "descriptor": copy.deepcopy(dict(descriptor)),
            "descriptor_sha256": descriptor_sha256,
            "current_item_pins": copy.deepcopy(pins),
            # In-memory only: materialization recomputes every response pin
            # from these exact current raw members rather than trusting a
            # reviewer-supplied association.
            "raw_members": list(raw_members),
        }
    if not out:
        raise SourceRecordManualComplementError(
            "current raw audit has no generated semantic groups"
        )
    return out


@dataclass(frozen=True)
class _StrictV11FullSpecRuntimeCoverage:
    """In-process strict receipt projection for one exact raw audit.

    This is deliberately not serialized as a sidecar credential.  It only
    tells the manual queue which groups have already been discharged by the
    fresh strict full-Spec route in this process; the same projection is
    recomputed before materialization.
    """

    component_judgment_keys: frozenset[str] = frozenset()
    semantic_model_judgment_keys: frozenset[str] = frozenset()


def _audit_repository_module() -> Any:
    """Load the closeout runtime authority lazily to avoid import cycles."""

    try:
        from scripts import audit_repository as repository
    except ModuleNotFoundError:  # pragma: no cover - direct-script fallback.
        import audit_repository as repository
    return repository


def _prepare_manual_complement_runtime(
    raw_audit: Mapping[str, Any], *, paper: str, paper_dir: Path
) -> object | None:
    """Prepare one in-memory strict runtime for a canonical current raw audit.

    A raw audit without the strict component ledger has no strict full-Spec
    route to mint, so it retains the lightweight overlay-only path.  The
    repository factory itself rejects alternate folders and noncanonical raw
    payloads; this helper deliberately does not manufacture a fallback
    capability from a path or a serialized receipt.
    """

    if not isinstance(raw_audit.get("theorem_realization_component_items"), list):
        return None
    try:
        repository = _audit_repository_module()
        return repository.prepare_current_strict_v11_full_spec_source_record_runtime(
            paper,
            paper_dir,
            raw_audit,
        )
    except Exception:  # noqa: BLE001 - normal callers retain the fail-closed fallback.
        return None


def _manual_complement_runtime_identity_context(
    runtime: object | None,
    raw_audit: Mapping[str, Any],
    *,
    paper: str,
    paper_dir: Path,
) -> object | None:
    """Return the canonical runtime capability, or reject a supplied impostor."""

    if runtime is None:
        return None
    try:
        repository = _audit_repository_module()
        context = (
            repository.current_strict_v11_full_spec_source_record_runtime_identity_context(
                runtime,
                paper,
                paper_dir,
                raw_audit,
            )
        )
    except Exception as exc:  # noqa: BLE001 - a runtime cannot degrade to a retry.
        raise SourceRecordManualComplementError(
            "manual-complement strict runtime identity validation raised "
            f"{type(exc).__name__}: {exc}"
        ) from exc
    if context is None:
        raise SourceRecordManualComplementError(
            "manual-complement strict runtime does not match the canonical current raw audit"
        )
    return context


def _finalize_manual_complement_runtime(runtime: object | None) -> None:
    """Reject output when an exact shared runtime changed during queue work."""

    if runtime is None:
        return
    try:
        repository = _audit_repository_module()
        findings = (
            repository.current_strict_v11_full_spec_source_record_runtime_mutation_findings(
                runtime
            )
        )
    except Exception as exc:  # noqa: BLE001 - finalization is a hard boundary.
        raise SourceRecordManualComplementError(
            "manual-complement strict runtime finalization raised "
            f"{type(exc).__name__}: {exc}"
        ) from exc
    if findings:
        detail = str(getattr(findings[0], "message", findings[0])).strip()
        raise SourceRecordManualComplementError(
            "manual-complement runtime inputs changed or could not be finalized"
            + (": " + detail if detail else "")
        )


def _finalize_manual_complement_write(
    runtime: object | None,
    raw_audit: Mapping[str, Any],
    *,
    paper: str,
    paper_dir: Path,
) -> None:
    """Run one final currentness check before a public result or CLI write."""

    if runtime is not None:
        _finalize_manual_complement_runtime(runtime)
        return
    try:
        try:
            from scripts import audit_evidence_integrity as evidence
        except ModuleNotFoundError:  # pragma: no cover - direct-script fallback.
            import audit_evidence_integrity as evidence
        identity_context = evidence.prepare_current_source_record_identity_context(
            paper_dir,
            paper,
            raw_audit,
        )
    except Exception as exc:  # noqa: BLE001 - output must not outrun currentness.
        raise SourceRecordManualComplementError(
            "manual-complement fallback currentness finalization raised "
            f"{type(exc).__name__}: {exc}"
        ) from exc
    if identity_context is None:
        raise SourceRecordManualComplementError(
            "manual-complement fallback currentness could not validate the canonical "
            "raw/map/watch inputs"
        )
    try:
        identity_error = evidence.current_source_record_identity_context_error(
            identity_context,
            paper_dir=paper_dir,
            paper=paper,
            current_raw_audit=raw_audit,
        )
    except Exception as exc:  # noqa: BLE001 - output must not outrun currentness.
        raise SourceRecordManualComplementError(
            "manual-complement fallback currentness revalidation raised "
            f"{type(exc).__name__}: {exc}"
        ) from exc
    if identity_error:
        raise SourceRecordManualComplementError(
            "manual-complement fallback currentness changed or could not be finalized: "
            + identity_error
        )


def _write_current_manual_complement_output(
    path: Path,
    contents: str,
    *,
    runtime: object | None,
    raw_audit: Mapping[str, Any],
    paper: str,
    paper_dir: Path,
) -> None:
    """Finalize current inputs and then atomically write one CLI output."""

    _finalize_manual_complement_write(
        runtime, raw_audit, paper=paper, paper_dir=paper_dir
    )
    _atomic_write(path, contents)


def _runtime_finalization_deferred(value: object | None) -> bool:
    """Accept the CLI's private handoff and reject every other opt-out."""

    if value is None:
        return False
    if value is not _MANUAL_COMPLEMENT_WRITE_BOUNDARY_DEFERRAL:
        raise SourceRecordManualComplementError(
            "manual-complement runtime finalization may be deferred only by the CLI write handoff"
        )
    return True


def _strict_runtime_key_set(value: object) -> frozenset[str] | None:
    """Normalize a repository-issued key set or reject the whole projection."""

    if not isinstance(value, (set, frozenset, tuple, list)):
        return None
    keys: set[str] = set()
    for raw_key in value:
        if not isinstance(raw_key, str) or not raw_key or raw_key != raw_key.strip():
            return None
        if raw_key in keys:
            return None
        keys.add(raw_key)
    return frozenset(keys)


def _strict_v11_full_spec_runtime_coverage(
    raw_audit: Mapping[str, Any],
    *,
    paper: str,
    paper_dir: Path,
    runtime: object | None = None,
) -> _StrictV11FullSpecRuntimeCoverage:
    """Get fresh strict coverage without accepting persisted receipt data.

    The repository capability constructs an exact live closeout context when
    the template CLI is used outside a larger closeout.  It consumes a shared
    context when one exists in the repository gate.  Raw JSON cannot recreate
    those Lean receipts, so any unavailable or malformed result deliberately
    leaves every group in the manual queue.
    """

    # A strict full-Spec component route is defined over the explicit
    # occurrence ledger.  Do not create a parent-only exception from an audit
    # that lacks that generator-owned ledger.
    if not isinstance(raw_audit.get("theorem_realization_component_items"), list):
        return _StrictV11FullSpecRuntimeCoverage()
    try:
        repository = _audit_repository_module()
        if runtime is None:
            coverage = repository.current_strict_v11_full_spec_source_record_coverage(
                paper,
                paper_dir,
                raw_audit,
            )
        else:
            coverage = (
                repository.current_strict_v11_full_spec_source_record_runtime_coverage(
                    runtime,
                    paper,
                    paper_dir,
                    raw_audit,
                )
            )
            if coverage is None:
                raise SourceRecordManualComplementError(
                    "manual-complement strict runtime does not match the canonical "
                    "current raw audit"
                )
        component_keys = _strict_runtime_key_set(
            getattr(coverage, "component_judgment_keys", None)
        )
        semantic_keys = _strict_runtime_key_set(
            getattr(coverage, "semantic_model_judgment_keys", None)
        )
    except SourceRecordManualComplementError:
        raise
    except Exception:  # noqa: BLE001 - no live receipt means no exemption.
        return _StrictV11FullSpecRuntimeCoverage()
    if component_keys is None or semantic_keys is None:
        return _StrictV11FullSpecRuntimeCoverage()
    return _StrictV11FullSpecRuntimeCoverage(
        component_judgment_keys=component_keys,
        semantic_model_judgment_keys=semantic_keys,
    )


def _strict_component_group_has_complete_raw_member_coverage(
    group: Mapping[str, Any],
    raw_audit: Mapping[str, Any],
    *,
    key: str,
) -> bool:
    """Require every raw group member to map to a strict material component.

    The strict projector proves component occurrences.  A generated response
    group can include another view of the same component (for example, a
    canonical theorem-facing mirror and its reusable boundary record) or an
    unrelated obligation under the same storage key.  Every member therefore
    needs a distinct exact generator-owned join to a material component:
    either its source-record section/item digest, or its source-contract
    association digest plus structural type.  The latter retains the exact
    relation for aggregate/mirror views that intentionally have no reusable
    item digest.  An unrelated formula, model, or field remains queued.
    """

    raw_members = group.get("raw_members")
    raw_components = raw_audit.get("theorem_realization_component_items")
    if not isinstance(raw_members, list) or not isinstance(raw_components, list):
        return False

    member_coordinates: list[
        tuple[tuple[str, str] | None, tuple[str, str] | None]
    ] = []
    for member in raw_members:
        if (
            not isinstance(member, tuple)
            or len(member) != 2
            or not isinstance(member[0], str)
            or not isinstance(member[1], Mapping)
        ):
            return False
        section = member[0]
        item_digest = _sha256(member[1].get("source_record_item_sha256"))
        association = member[1].get("source_contract_association")
        association_digest = (
            _sha256(association.get("association_sha256"))
            if isinstance(association, Mapping)
            else ""
        )
        structural_type = _sha256(member[1].get("structural_type_sha256"))
        direct_coordinate = (section, item_digest) if section and item_digest else None
        association_coordinate = (
            (association_digest, structural_type)
            if association_digest and structural_type
            else None
        )
        if direct_coordinate is None and association_coordinate is None:
            return False
        member_coordinates.append((direct_coordinate, association_coordinate))
    if not member_coordinates:
        return False

    component_coordinates: list[
        tuple[tuple[str, str] | None, tuple[str, str] | None]
    ] = []
    for component in raw_components:
        if (
            not isinstance(component, Mapping)
            or str(component.get("source_claim_component_role") or "").strip()
            != "material"
            or str(component.get("source_judgment_key") or "").strip() != key
        ):
            continue
        section = str(component.get("source_component_section") or "").strip()
        item_digest = _sha256(component.get("source_record_item_sha256"))
        association = component.get("source_contract_association")
        association_digest = (
            _sha256(association.get("association_sha256"))
            if isinstance(association, Mapping)
            else ""
        )
        structural_type = _sha256(
            component.get("source_claim_component_structural_type_sha256")
        )
        direct_coordinate = (section, item_digest) if section and item_digest else None
        association_coordinate = (
            (association_digest, structural_type)
            if association_digest and structural_type
            else None
        )
        if direct_coordinate is None and association_coordinate is None:
            continue
        component_coordinates.append((direct_coordinate, association_coordinate))
    if len(component_coordinates) < len(member_coordinates):
        return False

    # Treat each generator occurrence as consumable once. A duplicated raw
    # member cannot piggyback on the same strict receipt merely because it has
    # the same storage key or association digest.
    matches_component_to_member: dict[int, int] = {}

    def assign(member_index: int, seen: set[int]) -> bool:
        member_direct, member_association = member_coordinates[member_index]
        for component_index, (component_direct, component_association) in enumerate(
            component_coordinates
        ):
            if component_index in seen or not (
                (member_direct is not None and member_direct == component_direct)
                or (
                    member_association is not None
                    and member_association == component_association
                )
            ):
                continue
            seen.add(component_index)
            prior_member = matches_component_to_member.get(component_index)
            if prior_member is None or assign(prior_member, seen):
                matches_component_to_member[component_index] = member_index
                return True
        return False

    return all(assign(member_index, set()) for member_index in range(len(member_coordinates)))


def _strict_semantic_parent_group_is_semantic_only(
    group: Mapping[str, Any], *, key: str
) -> bool:
    """Allow parent credit only for a group with exactly its semantic member."""

    raw_members = group.get("raw_members")
    if not isinstance(raw_members, list) or len(raw_members) != 1:
        return False
    member = raw_members[0]
    return (
        isinstance(member, tuple)
        and len(member) == 2
        and member[0] == "semantic_model_items"
        and isinstance(member[1], Mapping)
        and str(member[1].get("judgment_key") or "").strip() == key
    )


def _strict_v11_full_spec_runtime_coverage_ledger(
    coverage: _StrictV11FullSpecRuntimeCoverage,
) -> dict[str, list[str]]:
    """Serialize queue accounting, never the underlying runtime receipts."""

    return {
        "component_judgment_keys": sorted(coverage.component_judgment_keys),
        "semantic_model_judgment_keys": sorted(
            coverage.semantic_model_judgment_keys
        ),
    }


def _strict_v11_full_spec_runtime_coverage_ledger_error(value: object) -> str:
    """Validate the template-only queue accounting shape."""

    if not isinstance(value, Mapping) or set(value) != {
        "component_judgment_keys",
        "semantic_model_judgment_keys",
    }:
        return "has an invalid strict full-Spec runtime coverage ledger"
    for field in ("component_judgment_keys", "semantic_model_judgment_keys"):
        keys = value.get(field)
        if not isinstance(keys, list) or any(
            not isinstance(key, str) or not key or key != key.strip()
            for key in keys
        ):
            return "has an invalid strict full-Spec runtime coverage ledger"
        if keys != sorted(set(keys)):
            return "has an invalid strict full-Spec runtime coverage ledger"
    return ""


def _semantic_model_item_from_raw_members(
    raw_members: object, *, key: str
) -> dict[str, Any] | None:
    """Return the one semantic-model member of an exact raw response group.

    Membership in the generated ``semantic_model_items`` section is the
    structural trigger.  No storage-key prefix, declaration name, binder, or
    function name participates in deciding whether semantic review is needed.
    """

    if not isinstance(raw_members, list):
        raise SourceRecordManualComplementError(
            f"{key}: current raw group has no complete raw members"
        )
    semantic_items: list[dict[str, Any]] = []
    for member in raw_members:
        if (
            not isinstance(member, tuple)
            or len(member) != 2
            or not isinstance(member[0], str)
            or not isinstance(member[1], Mapping)
        ):
            raise SourceRecordManualComplementError(
                f"{key}: current raw group has a malformed raw member"
            )
        if member[0] == "semantic_model_items":
            semantic_items.append(dict(member[1]))
    if not semantic_items:
        return None
    if len(semantic_items) != 1:
        raise SourceRecordManualComplementError(
            f"{key}: current raw group has multiple semantic-model members"
        )
    return semantic_items[0]


def _semantic_model_response_completeness_error(
    item: Mapping[str, Any], response: Mapping[str, Any], *, key: str
) -> str:
    """Apply the fast gate's shared semantic completeness contract.

    Association pins are generated immediately before this call, so a
    completed template remains unable to smuggle them in.  The lazy import
    avoids the current-revalidation import cycle while ensuring materialized
    evidence is accepted by the exact same semantic validator as the later
    integrity gate.
    """

    try:
        from scripts.audit_evidence_integrity import (
            semantic_model_judgment_completeness_errors,
        )
    except ModuleNotFoundError:  # pragma: no cover - direct script fallback.
        from audit_evidence_integrity import semantic_model_judgment_completeness_errors

    errors = semantic_model_judgment_completeness_errors(
        dict(item), dict(response)
    )
    if not errors:
        return ""
    return (
        f"{key}: semantic-model response fails the shared completeness contract: "
        + "; ".join(errors)
    )


def _authenticated_overlay_items(
    paper_dir: Path,
    paper: str,
    raw_audit: Mapping[str, Any],
    *,
    source_record_identity_context: object | None = None,
) -> dict[str, dict[str, dict[str, Any]]]:
    """Replay only loaders that authenticate their own semantic transport.

    Each loader recomputes its descriptor relation against ``raw_audit``.  The
    keys returned below merely identify the already-authenticated current
    response slot; they are never used to compare historical and current
    obligations.
    """

    try:
        from scripts import source_record_authenticated_overlay_union as overlay_union
    except ModuleNotFoundError:  # pragma: no cover - direct-script fallback.
        import source_record_authenticated_overlay_union as overlay_union
    try:
        lanes = overlay_union.load_authenticated_current_overlay_lanes(
            paper_dir,
            paper,
            raw_audit,
            source_record_identity_context=source_record_identity_context,
        )
        # A manual complement may omit a group only when exactly one
        # authenticated transport owns that current slot.  Do this before
        # converting loader-private items to ordinary dictionaries so a
        # stronger schema-2 lane cannot be silently overwritten by a legacy
        # differential/manual path.
        overlay_union.strict_authenticated_current_overlay_union(lanes)
    except overlay_union.SourceRecordAuthenticatedOverlayUnionError as exc:
        raise SourceRecordManualComplementError(str(exc)) from exc
    return {
        lane.label: {key: dict(value) for key, value in lane.items.items()}
        for lane in lanes
    }


def _effective_overlay_items(
    overlays: Mapping[str, Mapping[str, Mapping[str, Any]]]
) -> dict[str, dict[str, Any]]:
    """Flatten every authenticated lane while rejecting competing owners.

    The typed union already rejects overlaps in production.  Keep the same
    fail-closed rule here as well because tests and future lane registries may
    call this helper directly.  This deliberately has no lane-name or
    precedence policy: a newly registered authenticated lane is included
    automatically, and two lanes may not silently select a response by order.
    """

    effective: dict[str, dict[str, Any]] = {}
    owners: dict[str, str] = {}
    for raw_label, entries in overlays.items():
        label = str(raw_label).strip()
        if not label:
            raise SourceRecordManualComplementError(
                "authenticated overlay loader returned an empty lane label"
            )
        if not isinstance(entries, Mapping):
            raise SourceRecordManualComplementError(
                f"authenticated {label} overlay loader returned malformed entries"
            )
        for raw_key, value in entries.items():
            key = str(raw_key).strip()
            if not key or not isinstance(value, Mapping):
                raise SourceRecordManualComplementError(
                    f"authenticated {label} overlay loader returned a malformed item"
                )
            prior_owner = owners.get(key)
            if prior_owner is not None:
                raise SourceRecordManualComplementError(
                    "authenticated overlay lanes overlap at current semantic group "
                    f"`{key}` ({prior_owner} and {label})"
                )
            effective[key] = dict(value)
            owners[key] = label
    return effective


def _overlay_key_ledger(
    overlays: Mapping[str, Mapping[str, Mapping[str, Any]]]
) -> dict[str, list[str]]:
    return {
        label: sorted(str(key) for key in values)
        for label, values in sorted(overlays.items())
    }


def _current_manual_group_records(
    raw_audit: Mapping[str, Any],
    *,
    paper: str,
    paper_dir: Path,
    strict_full_spec_coverage: _StrictV11FullSpecRuntimeCoverage | None = None,
    source_record_identity_context: object | None = None,
) -> tuple[
    dict[str, dict[str, Any]],
    dict[str, list[str]],
    _StrictV11FullSpecRuntimeCoverage,
]:
    groups = _raw_groups(raw_audit, paper=paper, paper_dir=paper_dir)
    overlays = _authenticated_overlay_items(
        paper_dir,
        paper,
        raw_audit,
        source_record_identity_context=source_record_identity_context,
    )
    effective = _effective_overlay_items(overlays)
    unknown_overlay = sorted(set(effective) - set(groups))
    if unknown_overlay:
        raise SourceRecordManualComplementError(
            "authenticated overlay contains keys absent from the current raw group ledger: "
            + ", ".join(unknown_overlay[:5])
        )
    coverage = (
        strict_full_spec_coverage
        if strict_full_spec_coverage is not None
        else _strict_v11_full_spec_runtime_coverage(
            raw_audit, paper=paper, paper_dir=paper_dir
        )
    )
    strict_claimed_keys = (
        coverage.component_judgment_keys | coverage.semantic_model_judgment_keys
    )
    unknown_strict_keys = sorted(strict_claimed_keys - set(groups))
    if unknown_strict_keys:
        raise SourceRecordManualComplementError(
            "strict full-Spec runtime coverage contains keys absent from the "
            "current raw group ledger: "
            + ", ".join(unknown_strict_keys[:5])
        )

    # A key is omitted only when the strict receipt route covers its whole raw
    # response group.  The component and semantic-parent routes are separate
    # on purpose: a shared group remains manual unless one route represents
    # every generated member in that group.
    component_keys = frozenset(
        key
        for key in coverage.component_judgment_keys
        if _strict_component_group_has_complete_raw_member_coverage(
            groups[key], raw_audit, key=key
        )
    )
    semantic_keys = frozenset(
        key
        for key in coverage.semantic_model_judgment_keys
        if _strict_semantic_parent_group_is_semantic_only(groups[key], key=key)
    )
    effective_strict_coverage = _StrictV11FullSpecRuntimeCoverage(
        component_judgment_keys=component_keys,
        semantic_model_judgment_keys=semantic_keys,
    )
    covered_keys = set(effective) | set(component_keys) | set(semantic_keys)
    manual = {key: groups[key] for key in sorted(set(groups) - covered_keys)}
    return manual, _overlay_key_ledger(overlays), effective_strict_coverage


def _closure_attestation_requirement(
    candidate: RecordFieldClosureCompletionCandidate,
) -> dict[str, Any]:
    """Return immutable generated context for one parent review response."""

    return {
        "schema": 1,
        "closure_sha256": candidate.closure_sha256,
        "record_root": candidate.record_root,
        "field_component_count": len(candidate.field_components),
        "field_component_sha256s": sorted(
            component_sha
            for _field_key, _component_key, component_sha, _type_sha
            in candidate.field_components
        ),
    }


def _manual_closure_completion_candidates(
    raw_audit: Mapping[str, Any],
    manual: Mapping[str, Mapping[str, Any]],
) -> tuple[RecordFieldClosureCompletionCandidate, ...]:
    """Keep only non-overlay, non-overlapping exact field closures.

    The structural helper is deliberately unaware of existing authenticated
    overlays.  A template may compress a closure only when its semantic parent
    and *every* field are still current manual groups.  Intersecting closures
    remain manual rather than allowing one field to receive two parent routes.
    """

    manual_keys = set(manual)
    explicit_parent_route_field_keys = {
        str(item.get("judgment_key") or "").strip()
        for item in raw_audit.get("recursive_field_items") or []
        if isinstance(item, Mapping)
        and str(item.get("judgment_key") or "").strip()
        and isinstance(
            item.get(RECURSIVE_FIELD_EXPLICIT_PARENT_ROUTE_FIELD), Mapping
        )
    }
    eligible = [
        candidate
        for candidate in current_record_field_closure_completion_candidates(raw_audit)
        if candidate.semantic_model_judgment_key in manual_keys
        and candidate.field_keys.issubset(manual_keys)
        # An explicit parent-route receipt is a generated classification
        # boundary. Closure compression would otherwise synthesize the fixed
        # `semantic_model_review` child response below and erase the receipt's
        # exact `permitted_classifications`. Keep every such field in the
        # ordinary current-review ledger instead.
        and candidate.field_keys.isdisjoint(explicit_parent_route_field_keys)
    ]
    field_counts: dict[str, int] = {}
    for candidate in eligible:
        for field_key in candidate.field_keys:
            field_counts[field_key] = field_counts.get(field_key, 0) + 1
    return tuple(
        candidate
        for candidate in eligible
        if all(field_counts[field_key] == 1 for field_key in candidate.field_keys)
    )


def _current_manual_group_records_with_closure_completion(
    raw_audit: Mapping[str, Any],
    *,
    paper: str,
    paper_dir: Path,
    strict_full_spec_coverage: _StrictV11FullSpecRuntimeCoverage | None = None,
    source_record_identity_context: object | None = None,
) -> tuple[
    dict[str, dict[str, Any]],
    dict[str, list[str]],
    _StrictV11FullSpecRuntimeCoverage,
    tuple[RecordFieldClosureCompletionCandidate, ...],
]:
    """Return manual groups after only attested direct-parent field compression."""

    manual, overlay_ledger, effective_strict_coverage = _current_manual_group_records(
        raw_audit,
        paper=paper,
        paper_dir=paper_dir,
        strict_full_spec_coverage=strict_full_spec_coverage,
        source_record_identity_context=source_record_identity_context,
    )
    candidates = _manual_closure_completion_candidates(raw_audit, manual)
    compressed_field_keys = {
        field_key for candidate in candidates for field_key in candidate.field_keys
    }
    remaining = {
        key: group for key, group in manual.items() if key not in compressed_field_keys
    }
    return remaining, overlay_ledger, effective_strict_coverage, candidates


def _classification_requirements_from_group(
    group: Mapping[str, Any],
) -> list[dict[str, Any]]:
    """Project exact generated route requirements into the review template."""

    requirements: list[dict[str, Any]] = []
    raw_members = group.get("raw_members")
    if not isinstance(raw_members, list):
        return requirements
    for member in raw_members:
        if (
            not isinstance(member, tuple)
            or len(member) != 2
            or not isinstance(member[1], Mapping)
        ):
            continue
        route = member[1].get(RECURSIVE_FIELD_EXPLICIT_PARENT_ROUTE_FIELD)
        if isinstance(route, Mapping):
            requirements.append(copy.deepcopy(dict(route)))
    return sorted(
        requirements,
        key=lambda requirement: _canonical_digest(requirement),
    )


def _manual_current_complement_template(
    raw_audit: Mapping[str, Any],
    *,
    paper: str,
    paper_dir: Path,
    runtime: object | None = None,
    _write_boundary_deferral: object | None = None,
) -> dict[str, Any]:
    """Create a template, optionally under the CLI's private write handoff."""

    effective_runtime = (
        runtime
        if runtime is not None
        else _prepare_manual_complement_runtime(
            raw_audit, paper=paper, paper_dir=paper_dir
        )
    )
    source_record_identity_context = _manual_complement_runtime_identity_context(
        effective_runtime,
        raw_audit,
        paper=paper,
        paper_dir=paper_dir,
    )
    strict_full_spec_coverage = _strict_v11_full_spec_runtime_coverage(
        raw_audit,
        paper=paper,
        paper_dir=paper_dir,
        runtime=effective_runtime,
    )
    manual, overlay_ledger, effective_strict_coverage, closure_candidates = (
        _current_manual_group_records_with_closure_completion(
            raw_audit,
            paper=paper,
            paper_dir=paper_dir,
            strict_full_spec_coverage=strict_full_spec_coverage,
            source_record_identity_context=source_record_identity_context,
        )
    )
    raw_digest = _sha256(raw_audit.get("source_record_audit_sha256"))
    if not raw_digest:  # Established by _raw_groups, retained for local clarity.
        raise SourceRecordManualComplementError("current raw audit has no aggregate digest")
    records: dict[str, dict[str, Any]] = {}
    requirements_by_parent: dict[str, list[dict[str, Any]]] = {}
    for candidate in closure_candidates:
        requirements_by_parent.setdefault(
            candidate.semantic_model_judgment_key, []
        ).append(_closure_attestation_requirement(candidate))
    for key, group in manual.items():
        records[key] = {
            "current_group_semantic_descriptor": copy.deepcopy(group["descriptor"]),
            "current_group_semantic_descriptor_sha256": group["descriptor_sha256"],
            "current_item_pins": copy.deepcopy(group["current_item_pins"]),
            "reviewed_current_semantics": False,
            "reviewer": "",
            "validated_at": "",
            "review_notes": "",
            "response": {},
            "required_record_field_closure_attestations": copy.deepcopy(
                sorted(
                    requirements_by_parent.get(key, []),
                    key=lambda requirement: str(requirement["closure_sha256"]),
                )
            ),
            "classification_requirements": _classification_requirements_from_group(
                group
            ),
        }
    template = {
        "schema": SOURCE_RECORD_MANUAL_COMPLEMENT_SCHEMA,
        "artifact_kind": SOURCE_RECORD_MANUAL_COMPLEMENT_TEMPLATE_KIND,
        "policy_version": SOURCE_RECORD_MANUAL_COMPLEMENT_POLICY_VERSION,
        "paper": paper,
        "current_source_record_audit_sha256": raw_digest,
        "generated_judgment_keys_sha256": CURRENT.generated_judgment_keys_sha256(
            raw_audit
        ),
        "generated_judgment_surface_sha256": CURRENT.generated_judgment_surface_sha256(
            raw_audit
        ),
        "review_scope": SOURCE_RECORD_MANUAL_COMPLEMENT_SCOPE,
        "authenticated_overlay_current_keys": overlay_ledger,
        STRICT_V11_FULL_SPEC_RUNTIME_COVERAGE_FIELD: (
            _strict_v11_full_spec_runtime_coverage_ledger(
                effective_strict_coverage
            )
        ),
        "record_field_closure_completion_candidates": [
            candidate.descriptor() for candidate in closure_candidates
        ],
        "manual_current_groups": records,
        "reviewed_current_semantics": False,
        "reviewer": "",
        "validated_at": "",
        "review_notes": (
            "Every listed current group needs an explicit current response. "
            "Historical responses may be consulted as background only; they do not "
            "establish a match. Confirm the complete generated descriptor and item "
            "pins before marking a group reviewed. A semantic-model group with "
            "`required_record_field_closure_attestations` must also give one "
            "explicit source/Lean semantic attestation for every listed exact "
            "closure before its field groups can be materialized."
        ),
        "non_evidence_scaffold": True,
        "must_not_be_written_to_repository_sidecar": True,
    }
    if not _runtime_finalization_deferred(_write_boundary_deferral):
        _finalize_manual_complement_write(
            effective_runtime,
            raw_audit,
            paper=paper,
            paper_dir=paper_dir,
        )
    return template


def manual_current_complement_template(
    raw_audit: Mapping[str, Any],
    *,
    paper: str,
    paper_dir: Path,
    runtime: object | None = None,
) -> dict[str, Any]:
    """Create a non-evidence template for every current non-overlay group.

    Public callers receive a final runtime or fallback raw/map/watch check
    before the template returns. Only the CLI's private write handoff may
    defer it until immediately before its atomic write.
    """

    return _manual_current_complement_template(
        raw_audit,
        paper=paper,
        paper_dir=paper_dir,
        runtime=runtime,
    )


def _candidate_or_draft_error(
    value: object,
    *,
    label: str,
    allow_root_template_scaffold: bool = False,
    path: str = "",
) -> str:
    """Reject explicit non-final markers without inspecting navigation text.

    Filenames, theorem names, and review prose are not evidence and are never
    searched.  This only examines explicit serialized status/marker fields.
    The one allowed exception is a *fresh* template's two required scaffold
    flags at its root; its review fields are separately required to be empty.
    """

    if isinstance(value, Mapping):
        for raw_key, child in value.items():
            key = str(raw_key).strip()
            child_path = f"{path}.{key}" if path else key
            if key in _TEMPLATE_CANDIDATE_MARKERS and bool(child):
                return f"{label} is marked candidate/draft/non-evidence at `{child_path}`"
            if key in _NON_EVIDENCE_MARKERS and bool(child):
                is_allowed_scaffold = (
                    allow_root_template_scaffold
                    and not path
                    and key
                    in {
                        "non_evidence_scaffold",
                        "must_not_be_written_to_repository_sidecar",
                    }
                )
                if not is_allowed_scaffold:
                    return f"{label} is marked candidate/draft/non-evidence at `{child_path}`"
            if key in _TEMPLATE_DRAFT_TEXT_FIELDS:
                text = str(child or "").strip().lower()
                if any(marker in text for marker in ("candidate", "draft", "proposal")):
                    return f"{label} is marked candidate/draft/non-evidence at `{child_path}`"
            if error := _candidate_or_draft_error(
                child,
                label=label,
                allow_root_template_scaffold=False,
                path=child_path,
            ):
                return error
    elif isinstance(value, (list, tuple)):
        for index, child in enumerate(value):
            child_path = f"{path}[{index}]"
            if error := _candidate_or_draft_error(
                child,
                label=label,
                allow_root_template_scaffold=False,
                path=child_path,
            ):
                return error
    return ""


def _ordered_current_item_pins(
    value: object, *, label: str
) -> tuple[list[dict[str, Any]] | None, str]:
    """Validate the generated receipt list while preserving its declared order."""

    if not isinstance(value, list):
        return None, f"{label} current_item_pins is not a list"
    normalized: list[dict[str, Any]] = []
    seen: set[str] = set()
    expected_fields = {
        "kind",
        "source_record_item_digest_schema",
        "source_record_item_sha256",
    }
    for index, pin in enumerate(value):
        if not isinstance(pin, Mapping) or set(pin) != expected_fields:
            return None, f"{label} current_item_pins[{index}] has an unsupported shape"
        raw_kind = pin.get("kind")
        kind = raw_kind.strip() if isinstance(raw_kind, str) else ""
        schema = pin.get("source_record_item_digest_schema")
        raw_digest = pin.get("source_record_item_sha256")
        digest = _sha256(raw_digest)
        if (
            not kind
            or raw_kind != kind
            or not isinstance(schema, int)
            or isinstance(schema, bool)
            or schema != CURRENT.SOURCE_RECORD_ITEM_DIGEST_SCHEMA
            or not digest
            or raw_digest != digest
        ):
            return None, f"{label} current_item_pins[{index}] is malformed"
        normalized_pin = {
            "kind": kind,
            "source_record_item_digest_schema": schema,
            "source_record_item_sha256": digest,
        }
        encoded = json.dumps(normalized_pin, sort_keys=True, separators=(",", ":"))
        if encoded in seen:
            return None, f"{label} current_item_pins has a duplicate receipt"
        seen.add(encoded)
        normalized.append(normalized_pin)
    return normalized, ""


def _template_group_match_signature(
    entry: object, *, label: str
) -> tuple[str, str]:
    """Return the key-independent exact descriptor/ordered-receipt relation."""

    if not isinstance(entry, Mapping):
        return "", f"{label} is not an object"
    descriptor = entry.get("current_group_semantic_descriptor")
    descriptor_sha256 = _sha256(entry.get("current_group_semantic_descriptor_sha256"))
    if (
        not isinstance(descriptor, Mapping)
        or not descriptor_sha256
        or _canonical_digest(descriptor) != descriptor_sha256
    ):
        return "", f"{label} has a malformed semantic descriptor"
    pins, pins_error = _ordered_current_item_pins(
        entry.get("current_item_pins"), label=label
    )
    if pins_error or pins is None:
        return "", pins_error or f"{label} has malformed current item pins"
    # ``canonical_digest_payload`` is the audit's established canonical
    # descriptor equality.  Do *not* canonicalize the pin list: receipt order
    # is part of this bridge's declared relation.
    requirements = entry.get("classification_requirements")
    if not isinstance(requirements, list) or any(
        not isinstance(requirement, Mapping) for requirement in requirements
    ):
        return "", f"{label} has malformed classification requirements"
    signature = json.dumps(
        {
            "descriptor": canonical_digest_payload(descriptor),
            "ordered_current_item_pins": pins,
            "classification_requirements": canonical_digest_payload(requirements),
        },
        sort_keys=True,
        separators=(",", ":"),
    )
    return signature, ""


def _fresh_template_error(template: Mapping[str, Any], *, paper: str) -> str:
    """Validate that an input is an untouched current non-evidence template."""

    if template.get("schema") != SOURCE_RECORD_MANUAL_COMPLEMENT_SCHEMA:
        return "fresh manual-complement template has an unsupported schema"
    if template.get("artifact_kind") != SOURCE_RECORD_MANUAL_COMPLEMENT_TEMPLATE_KIND:
        return "fresh manual-complement template has the wrong artifact_kind"
    if template.get("policy_version") != SOURCE_RECORD_MANUAL_COMPLEMENT_POLICY_VERSION:
        return "fresh manual-complement template has the wrong policy version"
    if template.get("paper") != paper:
        return "fresh manual-complement template has the wrong paper"
    if (
        template.get("non_evidence_scaffold") is not True
        or template.get("must_not_be_written_to_repository_sidecar") is not True
    ):
        return "fresh manual-complement template must retain both non-evidence scaffold markers"
    if error := _candidate_or_draft_error(
        template,
        label="fresh manual-complement template",
        allow_root_template_scaffold=True,
    ):
        return error
    if template.get("reviewed_current_semantics") is not False:
        return "fresh manual-complement template is already marked reviewed"
    if any(str(template.get(field) or "").strip() for field in ("reviewer", "validated_at")):
        return "fresh manual-complement template carries completed reviewer metadata"
    for field in (
        "current_source_record_audit_sha256",
        "generated_judgment_keys_sha256",
        "generated_judgment_surface_sha256",
    ):
        if not _sha256(template.get(field)):
            return f"fresh manual-complement template has no valid `{field}`"
    if str(template.get("review_scope") or "").strip() != (
        SOURCE_RECORD_MANUAL_COMPLEMENT_SCOPE
    ):
        return "fresh manual-complement template has the wrong review scope"
    if not isinstance(template.get("authenticated_overlay_current_keys"), Mapping):
        return "fresh manual-complement template has no authenticated-overlay ledger"
    if error := _strict_v11_full_spec_runtime_coverage_ledger_error(
        template.get(STRICT_V11_FULL_SPEC_RUNTIME_COVERAGE_FIELD)
    ):
        return "fresh manual-complement template " + error
    groups = template.get("manual_current_groups")
    if not isinstance(groups, Mapping) or not groups:
        return "fresh manual-complement template has no manual current-group ledger"
    if error := _closure_completion_template_fields_error(template):
        return "fresh " + error
    for raw_key, entry in groups.items():
        key = str(raw_key).strip()
        if not key or raw_key != key or not isinstance(entry, Mapping):
            return "fresh manual-complement template has an invalid manual group key or record"
        _signature, signature_error = _template_group_match_signature(
            entry, label=f"fresh group `{key}`"
        )
        if signature_error:
            return signature_error
        if entry.get("reviewed_current_semantics") is not False:
            return f"fresh group `{key}` is already marked reviewed"
        if any(str(entry.get(field) or "").strip() for field in ("reviewer", "validated_at")):
            return f"fresh group `{key}` carries completed reviewer metadata"
        if entry.get("response") != {}:
            return f"fresh group `{key}` carries a nonempty response"
    return ""


_CURRENT_MANUAL_QUEUE_TEMPLATE_FIELDS = (
    "schema",
    "artifact_kind",
    "policy_version",
    "paper",
    "current_source_record_audit_sha256",
    "generated_judgment_keys_sha256",
    "generated_judgment_surface_sha256",
    "review_scope",
    "authenticated_overlay_current_keys",
    STRICT_V11_FULL_SPEC_RUNTIME_COVERAGE_FIELD,
    "record_field_closure_completion_candidates",
)
_CURRENT_MANUAL_QUEUE_GROUP_FIELDS = (
    "current_group_semantic_descriptor",
    "current_group_semantic_descriptor_sha256",
    "current_item_pins",
    "required_record_field_closure_attestations",
    "classification_requirements",
)


def _current_manual_queue_surface(template: Mapping[str, Any]) -> dict[str, Any]:
    """Return only generated queue facts, never reviewer-authored content."""

    groups = template.get("manual_current_groups")
    rendered_groups: dict[str, dict[str, Any]] = {}
    if isinstance(groups, Mapping):
        for raw_key, raw_entry in groups.items():
            key = str(raw_key).strip()
            if key and isinstance(raw_entry, Mapping):
                rendered_groups[key] = {
                    field: copy.deepcopy(raw_entry.get(field))
                    for field in _CURRENT_MANUAL_QUEUE_GROUP_FIELDS
                }
    return {
        **{
            field: copy.deepcopy(template.get(field))
            for field in _CURRENT_MANUAL_QUEUE_TEMPLATE_FIELDS
        },
        "manual_current_groups": rendered_groups,
    }


def current_manual_complement_queue_error(
    template: Mapping[str, Any],
    raw_audit: Mapping[str, Any],
    *,
    paper: str,
    paper_dir: Path,
    runtime: object | None = None,
) -> str:
    """Reject a template unless its generated queue equals the live one.

    A fresh or seeded template is a review aid, not historical evidence.  It
    may guide current work only when its raw receipt and every generated queue
    fact still agree with a newly reconstructed canonical current queue.  The
    comparison intentionally omits reviewer-authored fields and never uses a
    storage key, source name, or Lean declaration as a matching rule.
    """

    raw_digest = _sha256(raw_audit.get("source_record_audit_sha256"))
    template_digest = _sha256(template.get("current_source_record_audit_sha256"))
    if not raw_digest:
        return "current raw audit has no valid aggregate digest"
    if template_digest != raw_digest:
        return "manual-complement template is not bound to the current raw digest"
    try:
        expected = _manual_current_complement_template(
            raw_audit,
            paper=paper,
            paper_dir=paper_dir,
            runtime=runtime,
            _write_boundary_deferral=_MANUAL_COMPLEMENT_WRITE_BOUNDARY_DEFERRAL,
        )
    except SourceRecordManualComplementError as exc:
        return "could not reconstruct the live manual-complement queue: " + str(exc)
    if canonical_digest_payload(_current_manual_queue_surface(template)) != canonical_digest_payload(
        _current_manual_queue_surface(expected)
    ):
        return "manual-complement template does not equal the live current queue"
    return ""


def _completed_prior_template_error(template: Mapping[str, Any], *, paper: str) -> str:
    """Validate a completed historic template without binding it to current raw."""

    if template.get("schema") != SOURCE_RECORD_MANUAL_COMPLEMENT_SCHEMA:
        return "completed prior template has an unsupported schema"
    if template.get("artifact_kind") != SOURCE_RECORD_MANUAL_COMPLEMENT_TEMPLATE_KIND:
        return "completed prior template has the wrong artifact_kind"
    if template.get("policy_version") not in {
        SOURCE_RECORD_MANUAL_COMPLEMENT_POLICY_VERSION,
        _LEGACY_SOURCE_RECORD_MANUAL_COMPLEMENT_POLICY_VERSION,
    }:
        return "completed prior template has the wrong policy version"
    if template.get("paper") != paper:
        return "completed prior template has the wrong paper"
    if error := _candidate_or_draft_error(
        template, label="completed prior template"
    ):
        return error
    if any(bool(template.get(marker)) for marker in _NON_EVIDENCE_MARKERS):
        return "completed prior template is still marked candidate/draft/non-evidence"
    if template.get("reviewed_current_semantics") is not True:
        return "completed prior template must set reviewed_current_semantics: true"
    if any(
        not str(template.get(field) or "").strip()
        for field in ("reviewer", "validated_at")
    ):
        return "completed prior template lacks reviewer or validated_at"
    for field in (
        "current_source_record_audit_sha256",
        "generated_judgment_keys_sha256",
        "generated_judgment_surface_sha256",
    ):
        if not _sha256(template.get(field)):
            return f"completed prior template has no valid `{field}`"
    if str(template.get("review_scope") or "").strip() != (
        SOURCE_RECORD_MANUAL_COMPLEMENT_SCOPE
    ):
        return "completed prior template has the wrong review scope"
    if not isinstance(template.get("authenticated_overlay_current_keys"), Mapping):
        return "completed prior template has no authenticated-overlay ledger"
    # The runtime queue ledger was added after completed templates already in
    # circulation.  It never supplies semantic evidence or selects a rebind;
    # the crosswalk below remains exact-descriptor-plus-ordered-pin only.  A
    # legacy completed *prior* may therefore omit it, while every fresh or
    # materialized current template must carry and revalidate it.
    if STRICT_V11_FULL_SPEC_RUNTIME_COVERAGE_FIELD in template:
        if error := _strict_v11_full_spec_runtime_coverage_ledger_error(
            template.get(STRICT_V11_FULL_SPEC_RUNTIME_COVERAGE_FIELD)
        ):
            return "completed prior template " + error
    groups = template.get("manual_current_groups")
    if not isinstance(groups, Mapping) or not groups:
        return "completed prior template has no manual current-group ledger"
    if error := _closure_completion_template_fields_error(template):
        return "completed prior " + error
    for raw_key, entry in groups.items():
        key = str(raw_key).strip()
        if not key or raw_key != key or not isinstance(entry, Mapping):
            return "completed prior template has an invalid manual group key or record"
        if error := _template_group_match_signature(entry, label=f"completed prior group `{key}`")[1]:
            return error
        if entry.get("reviewed_current_semantics") is not True:
            return f"completed prior group `{key}` must mark current semantics reviewed"
        if any(
            not str(entry.get(field) or "").strip()
            for field in ("reviewer", "validated_at", "review_notes")
        ):
            return f"completed prior group `{key}` lacks reviewer, validated_at, or review_notes"
        response = entry.get("response")
        if not isinstance(response, Mapping):
            return f"completed prior group `{key}` has no object-valued response"
        if error := _candidate_or_draft_error(
            response, label=f"completed prior group `{key}` response"
        ):
            return error
        if not str(
            response.get("classification")
            or response.get("judgment")
            or response.get("verdict")
            or response.get("status")
            or ""
        ).strip():
            return f"completed prior group `{key}` response lacks a classification"
        if not str(response.get("reason") or "").strip():
            return f"completed prior group `{key}` response lacks a reason"
        if not str(response.get("source_location") or "").strip():
            return f"completed prior group `{key}` response lacks a source_location"
    return ""


def _strip_rebind_generated_response_credentials(value: object) -> object:
    """Deep-copy reviewer content while removing generated/raw transport fields."""

    if isinstance(value, Mapping):
        out: dict[str, object] = {}
        for raw_key, child in value.items():
            key = str(raw_key)
            if (
                key in _REBIND_RESPONSE_GENERATED_FIELDS
                or any(key.startswith(prefix) for prefix in _REBIND_RESPONSE_GENERATED_PREFIXES)
            ):
                continue
            out[key] = _strip_rebind_generated_response_credentials(child)
        return out
    if isinstance(value, list):
        return [_strip_rebind_generated_response_credentials(child) for child in value]
    if isinstance(value, tuple):
        return [_strip_rebind_generated_response_credentials(child) for child in value]
    return copy.deepcopy(value)


def _template_match_index(
    groups: Mapping[str, Any], *, label: str
) -> tuple[dict[str, list[str]] | None, str]:
    """Index a template solely by descriptor-plus-ordered-pin facts.

    The caller decides which classes need uniqueness.  A prior completed
    template can legitimately contain extra groups now supplied by an
    authenticated overlay, so duplicates outside the fresh complement must not
    make an unrelated fresh group selectable or unselectable.
    """

    index: dict[str, list[str]] = {}
    for raw_key, entry in groups.items():
        key = str(raw_key).strip()
        signature, error = _template_group_match_signature(entry, label=f"{label} group `{key}`")
        if error:
            return None, error
        index.setdefault(signature, []).append(key)
    return index, ""


def _rebind_completed_manual_current_complement_template(
    fresh_current_template: Mapping[str, Any],
    completed_prior_template: Mapping[str, Any],
    *,
    paper: str,
) -> tuple[dict[str, Any], dict[str, int]]:
    """Transfer one completed review into a fresh template through exact facts.

    This is intentionally a template-to-template operation, not a source audit
    shortcut.  It uses neither keys nor Lean names to choose a match: each
    every fresh group must form a unique bijection with one selected subset of
    the completed prior template on the complete canonical descriptor and the
    *ordered* current item receipts.  Prior groups not in the fresh complement
    are not copied or used as evidence; they can be legitimately covered by a
    current authenticated overlay.  The output retains every generated field
    from ``fresh_current_template`` and contains only copied human review
    fields.  Normal materialization subsequently reprojects all current raw
    association/transport pins.
    """

    if error := _fresh_template_error(fresh_current_template, paper=paper):
        raise SourceRecordManualComplementError(error)
    if error := _completed_prior_template_error(completed_prior_template, paper=paper):
        raise SourceRecordManualComplementError(error)
    fresh_groups = fresh_current_template.get("manual_current_groups")
    prior_groups = completed_prior_template.get("manual_current_groups")
    assert isinstance(fresh_groups, Mapping) and isinstance(prior_groups, Mapping)
    fresh_index, error = _template_match_index(
        fresh_groups, label="fresh manual-complement template"
    )
    if error or fresh_index is None:
        raise SourceRecordManualComplementError(error or "could not index fresh template")
    prior_index, error = _template_match_index(
        prior_groups, label="completed prior template"
    )
    if error or prior_index is None:
        raise SourceRecordManualComplementError(error or "could not index completed prior template")
    matches: dict[str, tuple[str, str]] = {}
    consumed_prior_keys: set[str] = set()
    for signature, fresh_keys in fresh_index.items():
        if len(fresh_keys) != 1:
            raise SourceRecordManualComplementError(
                "fresh manual-complement template has ambiguous duplicate "
                "descriptor/current-item-pin groups; a key or declaration name "
                "cannot select between them"
            )
        prior_keys = prior_index.get(signature, [])
        if len(prior_keys) != 1:
            if not prior_keys:
                raise SourceRecordManualComplementError(
                    "fresh manual-complement template has a group with no exact "
                    "descriptor/ordered-current-item-pin match in the completed prior template"
                )
            raise SourceRecordManualComplementError(
                "completed prior template has ambiguous duplicate "
                "descriptor/current-item-pin groups for a fresh manual group; "
                "a key or declaration name cannot select between them"
            )
        fresh_key = fresh_keys[0]
        prior_key = prior_keys[0]
        if prior_key in consumed_prior_keys:
            raise SourceRecordManualComplementError(
                "completed prior template would reuse one human review for multiple "
                "fresh manual groups"
            )
        consumed_prior_keys.add(prior_key)
        matches[signature] = (fresh_key, prior_key)

    rebound = copy.deepcopy(dict(fresh_current_template))
    # Completion changes the scaffold state, but all current generated receipt
    # fields, group keys, descriptors, pins, and overlay metadata remain from
    # the fresh template.
    rebound.pop("non_evidence_scaffold", None)
    rebound.pop("must_not_be_written_to_repository_sidecar", None)
    for field in _TEMPLATE_HUMAN_FIELDS:
        rebound[field] = copy.deepcopy(completed_prior_template.get(field))
    rebound_groups = rebound.get("manual_current_groups")
    assert isinstance(rebound_groups, dict)
    for fresh_key, prior_key in matches.values():
        fresh_entry = rebound_groups.get(fresh_key)
        prior_entry = prior_groups.get(prior_key)
        assert isinstance(fresh_entry, dict) and isinstance(prior_entry, Mapping)
        for field in _TEMPLATE_HUMAN_FIELDS:
            fresh_entry[field] = copy.deepcopy(prior_entry.get(field))
        response = prior_entry.get("response")
        assert isinstance(response, Mapping)
        stripped = _strip_rebind_generated_response_credentials(response)
        assert isinstance(stripped, Mapping)
        fresh_entry["response"] = dict(stripped)
    return rebound, {
        "fresh_group_count": len(fresh_groups),
        "matched_prior_group_count": len(consumed_prior_keys),
        "ignored_prior_group_count": len(prior_groups) - len(consumed_prior_keys),
    }


def rebind_completed_manual_current_complement_template(
    fresh_current_template: Mapping[str, Any],
    completed_prior_template: Mapping[str, Any],
    *,
    paper: str,
) -> dict[str, Any]:
    """Return the completed fresh template from the fail-closed crosswalk."""

    return _rebind_completed_manual_current_complement_template(
        fresh_current_template, completed_prior_template, paper=paper
    )[0]


def _seed_completed_manual_current_complement_template(
    fresh_current_template: Mapping[str, Any],
    completed_prior_template: Mapping[str, Any],
    *,
    paper: str,
) -> tuple[dict[str, Any], dict[str, int]]:
    """Seed a fresh non-evidence template from uniquely identical prior reviews.

    This is deliberately weaker than
    :func:`rebind_completed_manual_current_complement_template`: an unmatched
    or ambiguous fresh group is retained as an explicitly unreviewed current
    group instead of being selected through a name, key, or declaration
    spelling.  The result keeps the fresh template's non-evidence scaffold,
    so it cannot be materialized until a reviewer completes *every* current
    group.  Only group-level reviewer fields and a credential-stripped
    response are copied for a unique exact match.
    """

    if error := _fresh_template_error(fresh_current_template, paper=paper):
        raise SourceRecordManualComplementError(error)
    if error := _completed_prior_template_error(completed_prior_template, paper=paper):
        raise SourceRecordManualComplementError(error)
    fresh_groups = fresh_current_template.get("manual_current_groups")
    prior_groups = completed_prior_template.get("manual_current_groups")
    assert isinstance(fresh_groups, Mapping) and isinstance(prior_groups, Mapping)
    fresh_index, error = _template_match_index(
        fresh_groups, label="fresh manual-complement template"
    )
    if error or fresh_index is None:
        raise SourceRecordManualComplementError(error or "could not index fresh template")
    prior_index, error = _template_match_index(
        prior_groups, label="completed prior template"
    )
    if error or prior_index is None:
        raise SourceRecordManualComplementError(
            error or "could not index completed prior template"
        )

    seeded = copy.deepcopy(dict(fresh_current_template))
    seeded_groups = seeded.get("manual_current_groups")
    assert isinstance(seeded_groups, dict)
    consumed_prior_keys: set[str] = set()
    seeded_group_count = 0

    # Selection is based only on the canonical descriptor and ordered receipt
    # list.  Keys below identify the fresh record to update after selection;
    # they never participate in whether a prior response matches it.
    for signature, fresh_keys in fresh_index.items():
        prior_keys = prior_index.get(signature, [])
        is_unique = len(fresh_keys) == 1 and len(prior_keys) == 1
        for fresh_key in fresh_keys:
            fresh_entry = seeded_groups.get(fresh_key)
            assert isinstance(fresh_entry, dict)
            if not is_unique:
                fresh_entry["review_seed_status"] = (
                    "unreviewed_no_unique_completed_prior_match"
                )
                continue
            prior_key = prior_keys[0]
            if prior_key in consumed_prior_keys:
                # This should be impossible because an index key has one
                # signature, but retain a fail-closed path if its shape ever
                # changes.
                fresh_entry["review_seed_status"] = (
                    "unreviewed_no_unique_completed_prior_match"
                )
                continue
            prior_entry = prior_groups.get(prior_key)
            assert isinstance(prior_entry, Mapping)
            for field in _TEMPLATE_HUMAN_FIELDS:
                fresh_entry[field] = copy.deepcopy(prior_entry.get(field))
            response = prior_entry.get("response")
            assert isinstance(response, Mapping)
            stripped = _strip_rebind_generated_response_credentials(response)
            assert isinstance(stripped, Mapping)
            fresh_entry["response"] = dict(stripped)
            fresh_entry["review_seed_status"] = (
                "seeded_exact_descriptor_and_ordered_current_item_pins"
            )
            consumed_prior_keys.add(prior_key)
            seeded_group_count += 1

    summary = {
        "fresh_group_count": len(fresh_groups),
        "completed_prior_group_count": len(prior_groups),
        "seeded_group_count": seeded_group_count,
        "unresolved_group_count": len(fresh_groups) - seeded_group_count,
        "surplus_prior_group_count": len(prior_groups) - len(consumed_prior_keys),
    }
    # Do not carry the completed template's top-level reviewer metadata.  The
    # seed remains a fresh non-evidence review scaffold until all unresolved
    # groups receive an explicit current review.
    seeded["review_seed"] = {
        "schema": SOURCE_RECORD_MANUAL_COMPLEMENT_REVIEW_SEED_SCHEMA,
        "policy_version": SOURCE_RECORD_MANUAL_COMPLEMENT_REVIEW_SEED_POLICY_VERSION,
        "match_relation": SOURCE_RECORD_MANUAL_COMPLEMENT_REVIEW_SEED_MATCH_RELATION,
        **summary,
    }
    return seeded, summary


def seed_completed_manual_current_complement_template(
    fresh_current_template: Mapping[str, Any],
    completed_prior_template: Mapping[str, Any],
    *,
    paper: str,
) -> dict[str, Any]:
    """Return a non-evidence fresh template with only unique reviews seeded."""

    return _seed_completed_manual_current_complement_template(
        fresh_current_template, completed_prior_template, paper=paper
    )[0]


def _closure_completion_requirements_by_parent(
    candidates: Sequence[RecordFieldClosureCompletionCandidate],
) -> dict[str, list[dict[str, Any]]]:
    """Return exact generated requirements keyed only after structural selection."""

    result: dict[str, list[dict[str, Any]]] = {}
    for candidate in candidates:
        result.setdefault(candidate.semantic_model_judgment_key, []).append(
            _closure_attestation_requirement(candidate)
        )
    return {
        parent: sorted(
            requirements,
            key=lambda requirement: str(requirement["closure_sha256"]),
        )
        for parent, requirements in result.items()
    }


def _closure_completion_template_fields_error(
    template: Mapping[str, Any],
    *,
    candidates: Sequence[RecordFieldClosureCompletionCandidate] | None = None,
) -> str:
    """Validate generated closure context without accepting a human-selected route."""

    descriptors = template.get("record_field_closure_completion_candidates")
    if not isinstance(descriptors, list):
        return "manual-complement template has no closure-completion candidate ledger"
    groups = template.get("manual_current_groups")
    if not isinstance(groups, Mapping):
        return "manual-complement template has no manual group ledger for closure requirements"
    for index, descriptor in enumerate(descriptors):
        if not isinstance(descriptor, Mapping):
            return f"closure-completion candidate {index} is not an object"
        if descriptor.get("schema") != 1 or not _sha256(descriptor.get("closure_sha256")):
            return f"closure-completion candidate {index} has an invalid identity"
    for key, entry in groups.items():
        if not isinstance(entry, Mapping) or not isinstance(
            entry.get("required_record_field_closure_attestations"), list
        ):
            return (
                "manual-complement template group `"
                + str(key)
                + "` has no closure-attestation requirement list"
            )
    if candidates is None:
        return ""
    expected_descriptors = [candidate.descriptor() for candidate in candidates]
    if canonical_digest_payload(descriptors) != canonical_digest_payload(
        expected_descriptors
    ):
        return "manual-complement template has stale or mismatched closure-completion candidates"
    expected_by_parent = _closure_completion_requirements_by_parent(candidates)
    for key, entry in groups.items():
        assert isinstance(entry, Mapping)
        expected = expected_by_parent.get(str(key), [])
        actual = entry.get("required_record_field_closure_attestations")
        if canonical_digest_payload(actual) != canonical_digest_payload(expected):
            return (
                "manual-complement template group `"
                + str(key)
                + "` has stale or mismatched closure-attestation requirements"
            )
    return ""


def _closure_attestation_response_error(
    response: Mapping[str, Any],
    *,
    candidates: Sequence[RecordFieldClosureCompletionCandidate] | None,
) -> str:
    """Require an explicit substantive attestation for every generated closure."""

    attestations = response.get(RECORD_FIELD_CLOSURE_COMPLETION_ATTESTATIONS_FIELD)
    if candidates is None:
        # Review fragments and historic templates carry their generated context
        # elsewhere. The final current-template validator compares it to the
        # raw candidate set before materialization.
        return ""
    if not candidates:
        return (
            "response carries a record-field closure attestation without a current "
            "generated closure requirement"
            if attestations is not None
            else ""
        )
    if not isinstance(attestations, list) or len(attestations) != len(candidates):
        return "response lacks one explicit record-field closure attestation per requirement"
    by_digest = {candidate.closure_sha256: candidate for candidate in candidates}
    seen: set[str] = set()
    for attestation in attestations:
        if not isinstance(attestation, Mapping):
            return "response has a non-object record-field closure attestation"
        closure_sha = _sha256(attestation.get("closure_sha256"))
        candidate = by_digest.get(closure_sha)
        if candidate is None or closure_sha in seen:
            return "response has an unknown or duplicate record-field closure attestation"
        if error := closure_attestation_error(attestation, candidate=candidate):
            return error
        seen.add(closure_sha)
    return "" if seen == set(by_digest) else "response omits a required record-field closure attestation"


def _review_response_error(
    response: object,
    *,
    label: str,
    required_closure_candidates: Sequence[RecordFieldClosureCompletionCandidate]
    | None = None,
    materialization_template: bool = False,
    semantic_descriptor: object | None = None,
    classification_requirements: object | None = None,
) -> str:
    """Validate reviewer-authored content before it enters a completed template."""

    if not isinstance(response, Mapping):
        return f"{label} has no object-valued response"
    if error := _candidate_or_draft_error(response, label=f"{label} response"):
        return error
    if not str(
        response.get("classification")
        or response.get("judgment")
        or response.get("verdict")
        or response.get("status")
        or ""
    ).strip():
        return f"{label} response lacks a classification"
    if not str(response.get("reason") or "").strip():
        return f"{label} response lacks a reason"
    if not str(response.get("source_location") or "").strip():
        return f"{label} response lacks a source_location"
    if error := _classification_specific_response_error(
        response,
        semantic_descriptor=semantic_descriptor,
        classification_requirements=classification_requirements,
    ):
        return f"{label} {error}"
    if error := _closure_attestation_response_error(
        response, candidates=required_closure_candidates
    ):
        return f"{label} {error}"
    if materialization_template:
        # Association pins are deliberately left for the raw projection step:
        # it distinguishes a forbidden reviewer-supplied pin from a valid
        # generated replacement with the established error/path.  Template
        # transport and item pins still cannot be supplied by a reviewer.
        generated = [
            str(field)
            for field in response
            if str(field) in _RESPONSE_TRANSPORT_FIELDS
            or str(field).startswith("source_record_item_")
        ]
    else:
        generated = [
            str(field)
            for field in response
            if (
                str(field) in _REBIND_RESPONSE_GENERATED_FIELDS
                or any(
                    str(field).startswith(prefix)
                    for prefix in _REBIND_RESPONSE_GENERATED_PREFIXES
                )
            )
        ]
    if generated:
        return (
            f"{label} response carries "
            + (
                "generated/overlay transport fields: "
                if materialization_template
                else "generated/raw transport fields: "
            )
            + ", ".join(sorted(generated)[:5])
        )
    return ""


def _classification_specific_response_error(
    response: Mapping[str, Any],
    *,
    semantic_descriptor: object | None,
    classification_requirements: object | None,
) -> str:
    """Require route-owned fields as soon as a classification is selected.

    The descriptor is generated from the current raw group.  Reading only its
    explicit route records avoids guessing from a classification label while
    preventing a reviewed template from reaching materialization with fields
    that the shared target-disposition gate will necessarily reject.
    """

    route_records: list[Mapping[str, Any]] = []

    def visit(value: object) -> None:
        if isinstance(value, Mapping):
            route = value.get(RECURSIVE_FIELD_EXPLICIT_PARENT_ROUTE_FIELD)
            if isinstance(route, Mapping):
                route_records.append(route)
            for nested in value.values():
                visit(nested)
        elif isinstance(value, list):
            for nested in value:
                visit(nested)

    visit(semantic_descriptor)
    if classification_requirements is not None:
        if not isinstance(classification_requirements, list) or any(
            not isinstance(requirement, Mapping)
            for requirement in classification_requirements
        ):
            return "has malformed generated classification requirements"
        route_records.extend(classification_requirements)
    if not route_records:
        return ""
    classification = str(response.get("classification") or "").strip()
    for route in route_records:
        permitted = route.get("permitted_classifications")
        if (
            not isinstance(permitted, list)
            or not permitted
            or any(not str(item).strip() for item in permitted)
        ):
            return "has a malformed explicit-parent permitted classification set"
        permitted_values = {str(item).strip() for item in permitted}
        if classification not in permitted_values:
            return (
                "classification is not permitted by its current explicit-parent route"
            )
        convention_id = str(route.get("convention_id") or "").strip()
        convention_sha = _sha256(route.get("convention_sha256"))
        if classification == "approved_source_convention":
            ids = response.get("model_convention_ids")
            hashes = response.get("model_convention_sha256_by_id")
            if (
                not convention_id
                or not convention_sha
                or not isinstance(ids, list)
                or convention_id not in {str(item).strip() for item in ids}
                or not isinstance(hashes, Mapping)
                or _sha256(hashes.get(convention_id)) != convention_sha
            ):
                return (
                    "approved_source_convention lacks its exact convention id/hash"
                )
    return ""


def _completed_review_entry_error(entry: object, *, label: str) -> str:
    """Require one fully reviewed descriptor-and-pin bound current record."""

    _signature, signature_error = _template_group_match_signature(entry, label=label)
    if signature_error:
        return signature_error
    assert isinstance(entry, Mapping)  # established by _template_group_match_signature
    if entry.get("reviewed_current_semantics") is not True:
        return f"{label} must explicitly mark current semantics reviewed"
    if any(
        not str(entry.get(field) or "").strip()
        for field in ("reviewer", "validated_at", "review_notes")
    ):
        return f"{label} lacks reviewer, validated_at, or review_notes"
    return _review_response_error(
        entry.get("response"),
        label=label,
        semantic_descriptor=entry.get("current_group_semantic_descriptor"),
        classification_requirements=entry.get("classification_requirements"),
    )


def _seeded_template_for_fragment_merge_error(
    template: Mapping[str, Any], *, paper: str
) -> str:
    """Validate a non-evidence seed without treating its storage keys as IDs."""

    if template.get("schema") != SOURCE_RECORD_MANUAL_COMPLEMENT_SCHEMA:
        return "seeded manual-complement template has an unsupported schema"
    if template.get("artifact_kind") != SOURCE_RECORD_MANUAL_COMPLEMENT_TEMPLATE_KIND:
        return "seeded manual-complement template has the wrong artifact_kind"
    if template.get("policy_version") != SOURCE_RECORD_MANUAL_COMPLEMENT_POLICY_VERSION:
        return "seeded manual-complement template has the wrong policy version"
    if template.get("paper") != paper:
        return "seeded manual-complement template has the wrong paper"
    if (
        template.get("non_evidence_scaffold") is not True
        or template.get("must_not_be_written_to_repository_sidecar") is not True
    ):
        return "seeded manual-complement template must retain both non-evidence markers"
    if error := _candidate_or_draft_error(
        template,
        label="seeded manual-complement template",
        allow_root_template_scaffold=True,
    ):
        return error
    if template.get("reviewed_current_semantics") is not False:
        return "seeded manual-complement template is already marked completed"
    if any(str(template.get(field) or "").strip() for field in ("reviewer", "validated_at")):
        return "seeded manual-complement template carries completed root metadata"
    for field in (
        "current_source_record_audit_sha256",
        "generated_judgment_keys_sha256",
        "generated_judgment_surface_sha256",
    ):
        if not _sha256(template.get(field)):
            return f"seeded manual-complement template has no valid `{field}`"
    if str(template.get("review_scope") or "").strip() != (
        SOURCE_RECORD_MANUAL_COMPLEMENT_SCOPE
    ):
        return "seeded manual-complement template has the wrong review scope"
    if error := _strict_v11_full_spec_runtime_coverage_ledger_error(
        template.get(STRICT_V11_FULL_SPEC_RUNTIME_COVERAGE_FIELD)
    ):
        return "seeded manual-complement template " + error
    seed = template.get("review_seed")
    if not isinstance(seed, Mapping):
        return "seeded manual-complement template has no review_seed receipt"
    if (
        seed.get("schema") != SOURCE_RECORD_MANUAL_COMPLEMENT_REVIEW_SEED_SCHEMA
        or seed.get("policy_version")
        != SOURCE_RECORD_MANUAL_COMPLEMENT_REVIEW_SEED_POLICY_VERSION
        or seed.get("match_relation")
        != SOURCE_RECORD_MANUAL_COMPLEMENT_REVIEW_SEED_MATCH_RELATION
    ):
        return "seeded manual-complement template has an invalid review_seed identity"
    groups = template.get("manual_current_groups")
    if not isinstance(groups, Mapping) or not groups:
        return "seeded manual-complement template has no manual current-group ledger"
    seeded_count = 0
    unresolved_count = 0
    for raw_key, entry in groups.items():
        key = str(raw_key).strip()
        if not key or raw_key != key or not isinstance(entry, Mapping):
            return "seeded manual-complement template has an invalid group record"
        status = str(entry.get("review_seed_status") or "").strip()
        if status == "seeded_exact_descriptor_and_ordered_current_item_pins":
            if error := _completed_review_entry_error(entry, label=f"seeded group `{key}`"):
                return error
            seeded_count += 1
        elif status == "unreviewed_no_unique_completed_prior_match":
            if _template_group_match_signature(entry, label=f"unreviewed group `{key}`")[1]:
                return f"unreviewed group `{key}` has a malformed descriptor or pins"
            if entry.get("reviewed_current_semantics") is not False:
                return f"unreviewed group `{key}` is incorrectly marked reviewed"
            if any(
                str(entry.get(field) or "").strip()
                for field in ("reviewer", "validated_at", "review_notes")
            ) or entry.get("response") != {}:
                return f"unreviewed group `{key}` carries reviewer-authored content"
            unresolved_count += 1
        else:
            return f"seeded group `{key}` has an unsupported review_seed_status"
    if (
        seed.get("fresh_group_count") != len(groups)
        or seed.get("seeded_group_count") != seeded_count
        or seed.get("unresolved_group_count") != unresolved_count
        or seed.get("completed_prior_group_count") is None
        or seed.get("surplus_prior_group_count") is None
    ):
        return "seeded manual-complement template has inconsistent review_seed counts"
    return ""


def _review_fragment_error(
    fragment: object,
    *,
    paper: str,
    raw_digest: str,
    label: str,
) -> str:
    """Reject a fragment unless every entry is independently self-describing."""

    if not isinstance(fragment, Mapping):
        return f"{label} is not an object"
    if set(fragment) != {
        "schema",
        "artifact_kind",
        "paper",
        "current_source_record_audit_sha256",
        "entries",
    }:
        return f"{label} has unsupported top-level fields"
    if (
        fragment.get("schema") != SOURCE_RECORD_MANUAL_COMPLEMENT_REVIEW_FRAGMENT_SCHEMA
        or fragment.get("artifact_kind")
        != SOURCE_RECORD_MANUAL_COMPLEMENT_REVIEW_FRAGMENT_KIND
        or fragment.get("paper") != paper
        or _sha256(fragment.get("current_source_record_audit_sha256")) != raw_digest
    ):
        return f"{label} has an invalid identity or raw-audit receipt"
    if error := _candidate_or_draft_error(fragment, label=label):
        return error
    entries = fragment.get("entries")
    if not isinstance(entries, Mapping) or not entries:
        return f"{label} has no object-valued entries"
    seen_signatures: set[str] = set()
    for raw_address, entry in entries.items():
        address = str(raw_address).strip()
        if not address or raw_address != address:
            return f"{label} has an invalid entry address"
        if not isinstance(entry, Mapping):
            return f"{label} entry `{address}` is not an object"
        if "review_seed_status" in entry:
            return f"{label} entry `{address}` carries a seed status"
        if error := _completed_review_entry_error(entry, label=f"{label} entry `{address}`"):
            return error
        signature, signature_error = _template_group_match_signature(
            entry, label=f"{label} entry `{address}`"
        )
        if signature_error:
            return signature_error
        if signature in seen_signatures:
            return (
                f"{label} has duplicate descriptor/ordered-pin entries; an address "
                "or declaration name cannot choose between them"
            )
        seen_signatures.add(signature)
    return ""


def assemble_seeded_manual_current_complement_template(
    seeded_template: Mapping[str, Any],
    review_fragments: Sequence[Mapping[str, Any]],
    *,
    paper: str,
    reviewer: str,
    validated_at: str,
    review_notes: str,
) -> dict[str, Any]:
    """Complete a seed from independent current reviews without key matching.

    A fragment's address is only a serialization location.  Each fragment is
    matched to an unresolved seed record solely through its full canonical
    semantic descriptor and ordered current item receipts.  Every unresolved
    seed record must receive exactly one review; otherwise this function fails
    rather than returning a partially completed template.
    """

    if error := _seeded_template_for_fragment_merge_error(seeded_template, paper=paper):
        raise SourceRecordManualComplementError(error)
    root_reviewer = reviewer.strip()
    root_validated_at = validated_at.strip()
    root_notes = review_notes.strip()
    if not root_reviewer or not root_validated_at or not root_notes:
        raise SourceRecordManualComplementError(
            "fragment assembly requires nonempty reviewer, validated_at, and review_notes"
        )
    if not review_fragments:
        raise SourceRecordManualComplementError(
            "fragment assembly requires at least one review fragment"
        )
    seed_groups = seeded_template.get("manual_current_groups")
    assert isinstance(seed_groups, Mapping)  # established by seeded-template validation
    unresolved_by_signature: dict[str, str] = {}
    for key, entry in seed_groups.items():
        assert isinstance(entry, Mapping)
        if entry.get("review_seed_status") != "unreviewed_no_unique_completed_prior_match":
            continue
        signature, signature_error = _template_group_match_signature(
            entry, label=f"seeded group `{key}`"
        )
        assert not signature_error
        if signature in unresolved_by_signature:
            raise SourceRecordManualComplementError(
                "seeded template has duplicate unresolved descriptor/ordered-pin groups; "
                "a key or declaration name cannot choose between them"
            )
        unresolved_by_signature[signature] = str(key)

    raw_digest = _sha256(seeded_template.get("current_source_record_audit_sha256"))
    replacements: dict[str, Mapping[str, Any]] = {}
    for index, fragment in enumerate(review_fragments, start=1):
        label = f"review fragment {index}"
        if error := _review_fragment_error(
            fragment, paper=paper, raw_digest=raw_digest, label=label
        ):
            raise SourceRecordManualComplementError(error)
        entries = fragment.get("entries")
        assert isinstance(entries, Mapping)
        for address, entry in entries.items():
            assert isinstance(entry, Mapping)
            signature, signature_error = _template_group_match_signature(
                entry, label=f"{label} entry `{address}`"
            )
            assert not signature_error
            target_key = unresolved_by_signature.get(signature)
            if target_key is None:
                raise SourceRecordManualComplementError(
                    f"{label} entry `{address}` does not identify an unresolved seed group"
                )
            if signature in replacements:
                raise SourceRecordManualComplementError(
                    "multiple review fragments identify the same unresolved semantic "
                    "descriptor/ordered-pin group"
                )
            replacements[signature] = entry
    missing = sorted(set(unresolved_by_signature) - set(replacements))
    if missing:
        raise SourceRecordManualComplementError(
            "review fragments leave current semantic groups unreviewed: "
            + str(len(missing))
        )

    completed = copy.deepcopy(dict(seeded_template))
    completed.pop("non_evidence_scaffold", None)
    completed.pop("must_not_be_written_to_repository_sidecar", None)
    completed.pop("review_seed", None)
    completed["reviewed_current_semantics"] = True
    completed["reviewer"] = root_reviewer
    completed["validated_at"] = root_validated_at
    completed["review_notes"] = root_notes
    completed_groups = completed.get("manual_current_groups")
    assert isinstance(completed_groups, dict)
    for key, entry in completed_groups.items():
        assert isinstance(entry, dict)
        if entry.get("review_seed_status") == "unreviewed_no_unique_completed_prior_match":
            signature, signature_error = _template_group_match_signature(
                entry, label=f"seeded group `{key}`"
            )
            assert not signature_error
            fragment_entry = replacements[signature]
            for field in _TEMPLATE_HUMAN_FIELDS:
                entry[field] = copy.deepcopy(fragment_entry.get(field))
            entry["response"] = copy.deepcopy(dict(fragment_entry["response"]))
        entry.pop("review_seed_status", None)
    return completed


def _fresh_template_as_all_unreviewed_seed(
    fresh_current_template: Mapping[str, Any], *, paper: str
) -> dict[str, Any]:
    """Prepare a first-review template for descriptor-bound fragment assembly.

    A first current review has no completed predecessor to seed from.  It still
    needs the same fail-closed fragment matcher used by the reuse path: every
    group must be matched by its complete semantic descriptor and ordered raw
    item pins, never by its storage key or a Lean declaration name.
    """

    if error := _fresh_template_error(fresh_current_template, paper=paper):
        raise SourceRecordManualComplementError(error)
    seeded = copy.deepcopy(dict(fresh_current_template))
    groups = seeded.get("manual_current_groups")
    assert isinstance(groups, dict)
    for entry in groups.values():
        assert isinstance(entry, dict)
        entry["review_seed_status"] = "unreviewed_no_unique_completed_prior_match"
    seeded["review_seed"] = {
        "schema": SOURCE_RECORD_MANUAL_COMPLEMENT_REVIEW_SEED_SCHEMA,
        "policy_version": SOURCE_RECORD_MANUAL_COMPLEMENT_REVIEW_SEED_POLICY_VERSION,
        "match_relation": SOURCE_RECORD_MANUAL_COMPLEMENT_REVIEW_SEED_MATCH_RELATION,
        "fresh_group_count": len(groups),
        "completed_prior_group_count": 0,
        "seeded_group_count": 0,
        "unresolved_group_count": len(groups),
        "surplus_prior_group_count": 0,
    }
    return seeded


def assemble_fresh_manual_current_complement_template(
    fresh_current_template: Mapping[str, Any],
    review_fragments: Sequence[Mapping[str, Any]],
    *,
    paper: str,
    reviewer: str,
    validated_at: str,
    review_notes: str,
) -> dict[str, Any]:
    """Complete a first-review template from independently authored fragments.

    This is intentionally only a convenience wrapper around the existing seed
    assembler.  It creates an all-unreviewed seed first, so the subsequent
    merge retains the exact same descriptor-and-ordered-pin identity checks as
    seeded reuse and cannot select a response through its key or name.
    """

    return assemble_seeded_manual_current_complement_template(
        _fresh_template_as_all_unreviewed_seed(fresh_current_template, paper=paper),
        review_fragments,
        paper=paper,
        reviewer=reviewer,
        validated_at=validated_at,
        review_notes=review_notes,
    )


def _template_error(
    completed: Mapping[str, Any],
    raw_audit: Mapping[str, Any],
    *,
    paper: str,
    paper_dir: Path,
    strict_full_spec_coverage: _StrictV11FullSpecRuntimeCoverage | None = None,
    source_record_identity_context: object | None = None,
    runtime: object | None = None,
) -> str:
    if strict_full_spec_coverage is None:
        strict_full_spec_coverage = _strict_v11_full_spec_runtime_coverage(
            raw_audit,
            paper=paper,
            paper_dir=paper_dir,
            runtime=runtime,
        )
    if source_record_identity_context is None and runtime is not None:
        try:
            source_record_identity_context = _manual_complement_runtime_identity_context(
                runtime,
                raw_audit,
                paper=paper,
                paper_dir=paper_dir,
            )
        except SourceRecordManualComplementError as exc:
            return str(exc)
    if completed.get("schema") != SOURCE_RECORD_MANUAL_COMPLEMENT_SCHEMA:
        return "completed manual-complement template has an unsupported schema"
    if completed.get("artifact_kind") != SOURCE_RECORD_MANUAL_COMPLEMENT_TEMPLATE_KIND:
        return "completed manual-complement template has the wrong artifact_kind"
    if completed.get("policy_version") != SOURCE_RECORD_MANUAL_COMPLEMENT_POLICY_VERSION:
        return "completed manual-complement template has the wrong policy version"
    if completed.get("paper") != paper:
        return "completed manual-complement template has the wrong paper"
    if any(bool(completed.get(marker)) for marker in _NON_EVIDENCE_MARKERS):
        return "completed manual-complement template is still marked non-evidence"
    if completed.get("reviewed_current_semantics") is not True:
        return "completed manual-complement template must set reviewed_current_semantics: true"
    if not str(completed.get("reviewer") or "").strip() or not str(
        completed.get("validated_at") or ""
    ).strip():
        return "completed manual-complement template lacks reviewer or validated_at"
    if str(completed.get("review_scope") or "").strip() != (
        SOURCE_RECORD_MANUAL_COMPLEMENT_SCOPE
    ):
        return "completed manual-complement template has the wrong review scope"
    raw_digest = _sha256(raw_audit.get("source_record_audit_sha256"))
    if _sha256(completed.get("current_source_record_audit_sha256")) != raw_digest:
        return "completed manual-complement template is not bound to the current raw digest"
    try:
        expected_keys_digest = CURRENT.generated_judgment_keys_sha256(raw_audit)
        expected_surface_digest = CURRENT.generated_judgment_surface_sha256(raw_audit)
    except CURRENT.SourceRecordCurrentRevalidationError as exc:
        return f"could not recompute current generated judgment ledger: {exc}"
    if _sha256(completed.get("generated_judgment_keys_sha256")) != expected_keys_digest:
        return "completed manual-complement template has a stale current key ledger"
    if _sha256(completed.get("generated_judgment_surface_sha256")) != expected_surface_digest:
        return "completed manual-complement template has a stale current surface ledger"
    try:
        (
            expected_manual,
            expected_overlays,
            expected_strict_coverage,
            expected_closure_candidates,
        ) = (
            _current_manual_group_records_with_closure_completion(
                raw_audit,
                paper=paper,
                paper_dir=paper_dir,
                strict_full_spec_coverage=strict_full_spec_coverage,
                source_record_identity_context=source_record_identity_context,
            )
        )
    except SourceRecordManualComplementError as exc:
        return str(exc)
    if completed.get("authenticated_overlay_current_keys") != expected_overlays:
        return "completed manual-complement template has a stale authenticated-overlay ledger"
    if completed.get(STRICT_V11_FULL_SPEC_RUNTIME_COVERAGE_FIELD) != (
        _strict_v11_full_spec_runtime_coverage_ledger(expected_strict_coverage)
    ):
        return "completed manual-complement template has a stale strict full-Spec runtime coverage ledger"
    submitted = completed.get("manual_current_groups")
    if not isinstance(submitted, Mapping):
        return "completed manual-complement template has no object-valued manual group ledger"
    submitted_keys = {str(key).strip() for key in submitted}
    if submitted_keys != set(expected_manual):
        missing = sorted(set(expected_manual) - submitted_keys)
        extra = sorted(submitted_keys - set(expected_manual))
        return (
            "completed manual-complement template does not cover the exact current complement"
            + (f"; missing={missing[:5]}" if missing else "")
            + (f"; extra={extra[:5]}" if extra else "")
        )
    if error := _closure_completion_template_fields_error(
        completed, candidates=expected_closure_candidates
    ):
        return "completed " + error
    expected_closure_candidates_by_parent: dict[
        str, list[RecordFieldClosureCompletionCandidate]
    ] = {}
    for candidate in expected_closure_candidates:
        expected_closure_candidates_by_parent.setdefault(
            candidate.semantic_model_judgment_key, []
        ).append(candidate)
    for key, expected in expected_manual.items():
        entry = submitted.get(key)
        if not isinstance(entry, Mapping):
            return f"{key}: manual current-group record is not an object"
        descriptor = entry.get("current_group_semantic_descriptor")
        descriptor_sha256 = _sha256(
            entry.get("current_group_semantic_descriptor_sha256")
        )
        if (
            not isinstance(descriptor, Mapping)
            or _canonical_digest(descriptor) != descriptor_sha256
            or descriptor_sha256 != expected["descriptor_sha256"]
            or canonical_digest_payload(descriptor)
            != canonical_digest_payload(expected["descriptor"])
        ):
            return f"{key}: manual record has a stale or mismatched semantic descriptor"
        if entry.get("current_item_pins") != expected["current_item_pins"]:
            return f"{key}: manual record has stale or incomplete current item pins"
        expected_classification_requirements = (
            _classification_requirements_from_group(expected)
        )
        if canonical_digest_payload(entry.get("classification_requirements")) != (
            canonical_digest_payload(expected_classification_requirements)
        ):
            return (
                f"{key}: manual record has stale or incomplete classification requirements"
            )
        if entry.get("reviewed_current_semantics") is not True:
            return f"{key}: manual record must explicitly mark current semantics reviewed"
        if not str(entry.get("reviewer") or "").strip() or not str(
            entry.get("validated_at") or ""
        ).strip():
            return f"{key}: manual record lacks reviewer or validated_at"
        if not str(entry.get("review_notes") or "").strip():
            return f"{key}: manual record lacks review_notes"
        if error := _review_response_error(
            entry.get("response"),
            label=f"{key}: manual record",
            required_closure_candidates=expected_closure_candidates_by_parent.get(
                key, []
            ),
            materialization_template=True,
            semantic_descriptor=entry.get("current_group_semantic_descriptor"),
            classification_requirements=entry.get("classification_requirements"),
        ):
            return error
    return ""


def _materialize_manual_current_complement(
    raw_audit: Mapping[str, Any],
    completed_template: Mapping[str, Any],
    *,
    paper: str,
    paper_dir: Path,
    output_sidecar_path: Path,
    runtime: object | None = None,
    _write_boundary_deferral: object | None = None,
) -> dict[str, Any]:
    """Materialize ordinary evidence under the CLI's private write handoff."""

    effective_runtime = (
        runtime
        if runtime is not None
        else _prepare_manual_complement_runtime(
            raw_audit, paper=paper, paper_dir=paper_dir
        )
    )
    source_record_identity_context = _manual_complement_runtime_identity_context(
        effective_runtime,
        raw_audit,
        paper=paper,
        paper_dir=paper_dir,
    )
    strict_full_spec_coverage = _strict_v11_full_spec_runtime_coverage(
        raw_audit,
        paper=paper,
        paper_dir=paper_dir,
        runtime=effective_runtime,
    )
    if error := _template_error(
        completed_template,
        raw_audit,
        paper=paper,
        paper_dir=paper_dir,
        strict_full_spec_coverage=strict_full_spec_coverage,
        source_record_identity_context=source_record_identity_context,
    ):
        raise SourceRecordManualComplementError(error)
    _paper_path(output_sidecar_path, paper_dir, label="output sidecar")
    raw_digest = _sha256(raw_audit.get("source_record_audit_sha256"))
    statement_map_path = paper_dir / "audit" / "paper_statement_map.json"
    statement_map = (
        _read_json_object(statement_map_path) if statement_map_path.exists() else None
    )
    status_path = paper_dir / "status.json"
    status_payload = _read_json_object(status_path) if status_path.exists() else None
    regularity_context, _regularity_context_error = (
        load_configured_assumption_formalization_regularity_context(
            paper_dir,
            raw_audit,
            status_payload=status_payload,
        )
    )
    submitted = completed_template.get("manual_current_groups")
    assert isinstance(submitted, Mapping)  # established by _template_error
    expected_manual, _, _, closure_candidates = (
        _current_manual_group_records_with_closure_completion(
            raw_audit,
            paper=paper,
            paper_dir=paper_dir,
            strict_full_spec_coverage=strict_full_spec_coverage,
            source_record_identity_context=source_record_identity_context,
        )
    )
    all_groups = _raw_groups(raw_audit, paper=paper, paper_dir=paper_dir)
    result_items: dict[str, dict[str, Any]] = {}
    for key in sorted(submitted):
        entry = submitted[key]
        assert isinstance(entry, Mapping)  # established by _template_error
        response = copy.deepcopy(dict(entry["response"]))
        raw_group = expected_manual.get(str(key))
        raw_members = raw_group.get("raw_members") if isinstance(raw_group, Mapping) else None
        response, projection_error = project_source_record_response_association_pins(
            raw_members,
            response,
            judgment_key=key,
            reject_existing=True,
            statement_map=statement_map,
            configured_assumption_formalization_regularity_context=regularity_context,
        )
        if projection_error or response is None:
            raise SourceRecordManualComplementError(
                f"{key}: current raw association projection failed: {projection_error}"
            )
        for field in list(response):
            if field in _RESPONSE_TRANSPORT_FIELDS or field.startswith(
                "source_record_item_"
            ):
                response.pop(field)
        response["prompt_version"] = CURRENT.SOURCE_RECORD_V10_PROMPT_VERSION
        response["validator"] = str(entry["reviewer"]).strip()
        response["validated_at"] = str(entry["validated_at"]).strip()
        response["source_record_audit_sha256"] = raw_digest
        pins = entry["current_item_pins"]
        assert isinstance(pins, list)  # established by exact template validation
        if pins:
            response["source_record_item_digest_schema"] = (
                CURRENT.SOURCE_RECORD_ITEM_DIGEST_SCHEMA
            )
            response["source_record_item_sha256s"] = copy.deepcopy(pins)
            response["source_record_item_sha256"] = pins[0][
                "source_record_item_sha256"
            ]
        semantic_item = _semantic_model_item_from_raw_members(
            raw_members, key=str(key)
        )
        if semantic_item is not None:
            if error := _semantic_model_response_completeness_error(
                semantic_item, response, key=str(key)
            ):
                raise SourceRecordManualComplementError(error)
        result_items[str(key)] = response
    for candidate in closure_candidates:
        parent_response = result_items.get(candidate.semantic_model_judgment_key)
        if not isinstance(parent_response, Mapping):
            raise SourceRecordManualComplementError(
                "closure-completion parent response disappeared during materialization"
            )
        attestation = closure_attestation_for_candidate(
            parent_response, candidate=candidate
        )
        if attestation is None:
            raise SourceRecordManualComplementError(
                "closure-completion parent attestation failed current validation"
            )
        attestation_digest = closure_attestation_sha256(attestation)
        for (
            field_key,
            component_key,
            component_sha,
            structural_type_sha,
        ) in candidate.field_components:
            if field_key in result_items:
                raise SourceRecordManualComplementError(
                    "closure-completion field collides with an ordinary current response"
                )
            raw_group = all_groups.get(field_key)
            if not isinstance(raw_group, Mapping):
                raise SourceRecordManualComplementError(
                    "closure-completion field has no current generated group"
                )
            raw_members = raw_group.get("raw_members")
            response: dict[str, Any] = {
                "classification": "semantic_model_review",
                "reason": (
                    "Explicit parent closure attestation covers this exact generated "
                    "field occurrence."
                ),
                "source_location": str(attestation["source_location"]).strip(),
                RECORD_FIELD_CLOSURE_COMPLETION_RECEIPT_FIELD: {
                    "schema": RECORD_FIELD_CLOSURE_COMPLETION_RECEIPT_SCHEMA,
                    "closure_sha256": candidate.closure_sha256,
                    "attestation_sha256": attestation_digest,
                    "semantic_model_judgment_key": candidate.semantic_model_judgment_key,
                    "component_sha256": component_sha,
                    "structural_type_sha256": structural_type_sha,
                },
            }
            response, projection_error = project_source_record_response_association_pins(
                raw_members,
                response,
                judgment_key=field_key,
                reject_existing=True,
                statement_map=statement_map,
                configured_assumption_formalization_regularity_context=regularity_context,
            )
            if projection_error or response is None:
                raise SourceRecordManualComplementError(
                    "closure-completion field current raw association projection failed: "
                    + str(projection_error)
                )
            response["prompt_version"] = CURRENT.SOURCE_RECORD_V10_PROMPT_VERSION
            response["validator"] = str(completed_template["reviewer"]).strip()
            response["validated_at"] = str(completed_template["validated_at"]).strip()
            response["source_record_audit_sha256"] = raw_digest
            receipt_error = closure_completion_receipt_error(
                response.get(RECORD_FIELD_CLOSURE_COMPLETION_RECEIPT_FIELD),
                candidate=candidate,
                field_key=field_key,
                component_key=component_key,
                component_sha256=component_sha,
                structural_type_sha256=structural_type_sha,
                attestation_sha256=attestation_digest,
            )
            if receipt_error:
                raise SourceRecordManualComplementError(
                    "closure-completion field has an invalid exact closure receipt: "
                    + receipt_error
                )
            pins = raw_group.get("current_item_pins")
            if not isinstance(pins, list):
                raise SourceRecordManualComplementError(
                    "closure-completion field has malformed current item pins"
                )
            if pins:
                response["source_record_item_digest_schema"] = (
                    CURRENT.SOURCE_RECORD_ITEM_DIGEST_SCHEMA
                )
                response["source_record_item_sha256s"] = copy.deepcopy(pins)
                response["source_record_item_sha256"] = pins[0][
                    "source_record_item_sha256"
                ]
            # Aggregate-only field groups deliberately have no reusable
            # item pin. This path is still exact: the current aggregate raw
            # digest plus the validated closure receipt bind the parent,
            # occurrence component, structural type, and parent attestation.
            result_items[field_key] = response
    result = {
        "schema": 1,
        "paper": paper,
        "prompt_version": CURRENT.SOURCE_RECORD_V10_PROMPT_VERSION,
        "source_record_audit_sha256": raw_digest,
        FORMALIZATION_REVIEW_PROTOCOL_FIELD: formalization_review_protocol_digest(),
        "validator": str(completed_template["reviewer"]).strip(),
        "validated_at": str(completed_template["validated_at"]).strip(),
        "comment": (
            "Ordinary current responses for every generated v10 group not supplied "
            "by an authenticated semantic-reuse overlay. Each response was manually "
            "bound to the current complete semantic descriptor and current raw item pins. "
            "A generated record-field response is present only when an exact direct "
            "semantic parent supplied a current closure attestation."
        ),
        "manual_current_complement": {
            "schema": SOURCE_RECORD_MANUAL_COMPLEMENT_SCHEMA,
            "policy_version": SOURCE_RECORD_MANUAL_COMPLEMENT_POLICY_VERSION,
            "completed_template_review_scope": SOURCE_RECORD_MANUAL_COMPLEMENT_SCOPE,
            "current_source_record_audit_sha256": raw_digest,
            "generated_judgment_keys_sha256": CURRENT.generated_judgment_keys_sha256(
                raw_audit
            ),
            "generated_judgment_surface_sha256": CURRENT.generated_judgment_surface_sha256(
                raw_audit
            ),
            "template_reviewer": str(completed_template["reviewer"]).strip(),
            "template_validated_at": str(completed_template["validated_at"]).strip(),
            "output_sidecar_path": _relative_paper_path(output_sidecar_path, paper_dir),
            "record_field_closure_completion_count": len(closure_candidates),
            "record_field_closure_completion_field_count": sum(
                len(candidate.field_components) for candidate in closure_candidates
            ),
        },
        "items": result_items,
    }
    if not _runtime_finalization_deferred(_write_boundary_deferral):
        _finalize_manual_complement_write(
            effective_runtime,
            raw_audit,
            paper=paper,
            paper_dir=paper_dir,
        )
    return result


def materialize_manual_current_complement(
    raw_audit: Mapping[str, Any],
    completed_template: Mapping[str, Any],
    *,
    paper: str,
    paper_dir: Path,
    output_sidecar_path: Path,
    runtime: object | None = None,
) -> dict[str, Any]:
    """Convert an explicitly completed current review into ordinary evidence.

    Public callers receive a final runtime or fallback raw/map/watch check
    before ordinary evidence returns. Only the CLI's private write handoff may
    defer it until immediately before its atomic write.
    """

    return _materialize_manual_current_complement(
        raw_audit,
        completed_template,
        paper=paper,
        paper_dir=paper_dir,
        output_sidecar_path=output_sidecar_path,
        runtime=runtime,
    )


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description=(
            "Generate or materialize the manual current complement of authenticated "
            "v10 semantic-reuse overlays without rerunning the raw source audit."
        )
    )
    parser.add_argument("--root", type=Path, default=ROOT)
    parser.add_argument("--paper", required=True)
    parser.add_argument("--raw-audit", type=Path)
    mode = parser.add_mutually_exclusive_group(required=True)
    mode.add_argument(
        "--write-template",
        type=Path,
        help="write a non-evidence current-review template inside the paper",
    )
    mode.add_argument(
        "--completed-template",
        type=Path,
        help="completed template to validate/materialize into ordinary evidence",
    )
    mode.add_argument(
        "--rebind-completed-prior-template",
        type=Path,
        help=(
            "completed prior template to crosswalk into --fresh-template through "
            "exact descriptor and ordered current-item-pin equality"
        ),
    )
    mode.add_argument(
        "--seed-completed-prior-template",
        type=Path,
        help=(
            "completed prior template from which to seed uniquely identical groups "
            "in --fresh-template; unmatched groups remain explicitly unreviewed"
        ),
    )
    mode.add_argument(
        "--assemble-seeded-template",
        type=Path,
        help=(
            "non-evidence review seed to complete from descriptor-and-pin bound "
            "current review fragments"
        ),
    )
    mode.add_argument(
        "--assemble-fresh-template",
        type=Path,
        help=(
            "fresh non-evidence template to complete from descriptor-and-pin "
            "bound current review fragments"
        ),
    )
    mode.add_argument(
        "--assemble-fresh-template-and-materialize",
        type=Path,
        help=(
            "fresh non-evidence template to complete from descriptor-and-pin "
            "bound current review fragments and materialize directly into the "
            "canonical ordinary source-record sidecar in one strict runtime"
        ),
    )
    parser.add_argument(
        "--fresh-template",
        type=Path,
        help=(
            "fresh non-evidence template required with a completed-prior "
            "template rebind or seed mode"
        ),
    )
    parser.add_argument(
        "--out",
        type=Path,
        help=(
            "output path; required with --completed-template or "
            "a completed-prior template crosswalk/seed mode"
        ),
    )
    parser.add_argument(
        "--review-fragment",
        type=Path,
        action="append",
        help=(
            "current manual-review fragment used with an assemble-template mode; "
            "repeat once per fragment"
        ),
    )
    parser.add_argument(
        "--completed-reviewer",
        help="root reviewer label required while assembling a completed template",
    )
    parser.add_argument(
        "--completed-at",
        help="root validation timestamp required while assembling a completed template",
    )
    parser.add_argument(
        "--completed-review-notes",
        help="root review note required while assembling a completed template",
    )
    parser.add_argument(
        "--write",
        action="store_true",
        help="write --out after validation; otherwise perform a dry validation",
    )
    return parser.parse_args()


def main() -> int:
    args = parse_args()
    root = args.root.resolve()
    paper_dir = root / "papers" / args.paper
    try:
        if args.assemble_fresh_template_and_materialize is not None:
            if args.fresh_template is not None:
                raise SourceRecordManualComplementError(
                    "--fresh-template is not used with "
                    "--assemble-fresh-template-and-materialize"
                )
            if args.out is None or not args.review_fragment:
                raise SourceRecordManualComplementError(
                    "--assemble-fresh-template-and-materialize requires --out and at "
                    "least one --review-fragment"
                )
            fresh_path = _paper_path(
                args.assemble_fresh_template_and_materialize,
                paper_dir,
                label="--assemble-fresh-template-and-materialize",
            )
            fragment_paths = [
                _paper_path(path, paper_dir, label="--review-fragment")
                for path in args.review_fragment
            ]
            output_path = _paper_path(args.out, paper_dir, label="--out")
            canonical_sidecar_path = (
                paper_dir / "audit" / "source_record_match_llm.json"
            ).resolve()
            if output_path != canonical_sidecar_path:
                raise SourceRecordManualComplementError(
                    "--assemble-fresh-template-and-materialize must write the "
                    "canonical ordinary source-record sidecar "
                    "audit/source_record_match_llm.json"
                )
            if output_path in {fresh_path, *fragment_paths}:
                raise SourceRecordManualComplementError(
                    "canonical ordinary source-record sidecar must differ from every "
                    "fresh-template and review-fragment input"
                )
            fresh_template = _read_json_object(fresh_path)
            raw_path = _paper_path(
                args.raw_audit or paper_dir / "audit" / "source_record_audit.json",
                paper_dir,
                label="--raw-audit",
            )
            raw_audit = _read_json_object(raw_path)
            # This is deliberately the only strict-runtime factory call in the
            # combined path. Every subsequent queue, descriptor/pin, and
            # materialization check receives this same nonserializable capability.
            runtime = _prepare_manual_complement_runtime(
                raw_audit, paper=args.paper, paper_dir=paper_dir
            )
            if error := _fresh_template_error(fresh_template, paper=args.paper):
                raise SourceRecordManualComplementError(error)
            if error := current_manual_complement_queue_error(
                fresh_template,
                raw_audit,
                paper=args.paper,
                paper_dir=paper_dir,
                runtime=runtime,
            ):
                raise SourceRecordManualComplementError(
                    "fresh template cannot guide the current queue: " + error
                )
            completed = assemble_fresh_manual_current_complement_template(
                fresh_template,
                [_read_json_object(path) for path in fragment_paths],
                paper=args.paper,
                reviewer=str(args.completed_reviewer or ""),
                validated_at=str(args.completed_at or ""),
                review_notes=str(args.completed_review_notes or ""),
            )
            # The private materializer replays the complete current queue and
            # checks every assembled descriptor/pin again. Do not preflight it
            # separately here: that would repeat the same full ledger work.
            result = _materialize_manual_current_complement(
                raw_audit,
                completed,
                paper=args.paper,
                paper_dir=paper_dir,
                output_sidecar_path=output_path,
                runtime=runtime,
                _write_boundary_deferral=_MANUAL_COMPLEMENT_WRITE_BOUNDARY_DEFERRAL,
            )
            if args.write:
                _write_current_manual_complement_output(
                    output_path,
                    json.dumps(result, indent=2, sort_keys=True) + "\n",
                    runtime=runtime,
                    raw_audit=raw_audit,
                    paper=args.paper,
                    paper_dir=paper_dir,
                )
                print(
                    f"{args.paper}: assembled fresh review fragments and wrote ordinary "
                    f"current source-record evidence to {output_path} "
                    f"({len(result['items'])} manual groups)"
                )
            else:
                print(
                    f"{args.paper}: fresh review fragments assemble and materialize "
                    "against the current queue; rerun with --write"
                )
            return 0
        if args.assemble_seeded_template is not None:
            if args.fresh_template is not None:
                raise SourceRecordManualComplementError(
                    "--fresh-template is not used with --assemble-seeded-template"
                )
            if args.out is None or not args.review_fragment:
                raise SourceRecordManualComplementError(
                    "--assemble-seeded-template requires --out and at least one --review-fragment"
                )
            seeded_path = _paper_path(
                args.assemble_seeded_template,
                paper_dir,
                label="--assemble-seeded-template",
            )
            fragment_paths = [
                _paper_path(path, paper_dir, label="--review-fragment")
                for path in args.review_fragment
            ]
            output_path = _paper_path(args.out, paper_dir, label="--out")
            protected = {
                seeded_path,
                *fragment_paths,
                paper_dir / "audit" / "source_record_match_llm.json",
            }
            if output_path in protected:
                raise SourceRecordManualComplementError(
                    "assembled completed-template output must differ from every input and "
                    "from the canonical ordinary source-record sidecar"
                )
            seeded_template = _read_json_object(seeded_path)
            raw_path = _paper_path(
                args.raw_audit or paper_dir / "audit" / "source_record_audit.json",
                paper_dir,
                label="--raw-audit",
            )
            raw_audit = _read_json_object(raw_path)
            runtime = _prepare_manual_complement_runtime(
                raw_audit, paper=args.paper, paper_dir=paper_dir
            )
            if error := _seeded_template_for_fragment_merge_error(
                seeded_template, paper=args.paper
            ):
                raise SourceRecordManualComplementError(error)
            if error := current_manual_complement_queue_error(
                seeded_template,
                raw_audit,
                paper=args.paper,
                paper_dir=paper_dir,
                runtime=runtime,
            ):
                raise SourceRecordManualComplementError(
                    "seeded template cannot guide the current queue: " + error
                )
            completed = assemble_seeded_manual_current_complement_template(
                seeded_template,
                [_read_json_object(path) for path in fragment_paths],
                paper=args.paper,
                reviewer=str(args.completed_reviewer or ""),
                validated_at=str(args.completed_at or ""),
                review_notes=str(args.completed_review_notes or ""),
            )
            if error := _template_error(
                completed,
                raw_audit,
                paper=args.paper,
                paper_dir=paper_dir,
                runtime=runtime,
            ):
                raise SourceRecordManualComplementError(
                    "assembled completed template failed current validation: " + error
                )
            if args.write:
                _write_current_manual_complement_output(
                    output_path,
                    json.dumps(completed, indent=2, sort_keys=True) + "\n",
                    runtime=runtime,
                    raw_audit=raw_audit,
                    paper=args.paper,
                    paper_dir=paper_dir,
                )
                print(
                    f"{args.paper}: wrote assembled completed manual-complement template "
                    f"to {output_path} ({len(completed['manual_current_groups'])} groups)"
                )
            else:
                print(
                    f"{args.paper}: current review fragments assemble and validate; rerun with --write"
                )
            return 0
        if args.assemble_fresh_template is not None:
            if args.fresh_template is not None:
                raise SourceRecordManualComplementError(
                    "--fresh-template is not used with --assemble-fresh-template"
                )
            if args.out is None or not args.review_fragment:
                raise SourceRecordManualComplementError(
                    "--assemble-fresh-template requires --out and at least one --review-fragment"
                )
            fresh_path = _paper_path(
                args.assemble_fresh_template,
                paper_dir,
                label="--assemble-fresh-template",
            )
            fragment_paths = [
                _paper_path(path, paper_dir, label="--review-fragment")
                for path in args.review_fragment
            ]
            output_path = _paper_path(args.out, paper_dir, label="--out")
            protected = {
                fresh_path,
                *fragment_paths,
                paper_dir / "audit" / "source_record_match_llm.json",
            }
            if output_path in protected:
                raise SourceRecordManualComplementError(
                    "assembled completed-template output must differ from every input and "
                    "from the canonical ordinary source-record sidecar"
                )
            fresh_template = _read_json_object(fresh_path)
            raw_path = _paper_path(
                args.raw_audit or paper_dir / "audit" / "source_record_audit.json",
                paper_dir,
                label="--raw-audit",
            )
            raw_audit = _read_json_object(raw_path)
            runtime = _prepare_manual_complement_runtime(
                raw_audit, paper=args.paper, paper_dir=paper_dir
            )
            if error := _fresh_template_error(fresh_template, paper=args.paper):
                raise SourceRecordManualComplementError(error)
            if error := current_manual_complement_queue_error(
                fresh_template,
                raw_audit,
                paper=args.paper,
                paper_dir=paper_dir,
                runtime=runtime,
            ):
                raise SourceRecordManualComplementError(
                    "fresh template cannot guide the current queue: " + error
                )
            completed = assemble_fresh_manual_current_complement_template(
                fresh_template,
                [_read_json_object(path) for path in fragment_paths],
                paper=args.paper,
                reviewer=str(args.completed_reviewer or ""),
                validated_at=str(args.completed_at or ""),
                review_notes=str(args.completed_review_notes or ""),
            )
            if error := _template_error(
                completed,
                raw_audit,
                paper=args.paper,
                paper_dir=paper_dir,
                runtime=runtime,
            ):
                raise SourceRecordManualComplementError(
                    "assembled completed template failed current validation: " + error
                )
            if args.write:
                _write_current_manual_complement_output(
                    output_path,
                    json.dumps(completed, indent=2, sort_keys=True) + "\n",
                    runtime=runtime,
                    raw_audit=raw_audit,
                    paper=args.paper,
                    paper_dir=paper_dir,
                )
                print(
                    f"{args.paper}: wrote assembled completed manual-complement template "
                    f"to {output_path} ({len(completed['manual_current_groups'])} groups)"
                )
            else:
                print(
                    f"{args.paper}: current review fragments assemble and validate; rerun with --write"
                )
            return 0
        if args.seed_completed_prior_template is not None:
            if args.raw_audit is not None:
                raise SourceRecordManualComplementError(
                    "--raw-audit is not used with --seed-completed-prior-template"
                )
            if args.fresh_template is None or args.out is None:
                raise SourceRecordManualComplementError(
                    "--seed-completed-prior-template requires --fresh-template and --out"
                )
            prior_path = _paper_path(
                args.seed_completed_prior_template,
                paper_dir,
                label="--seed-completed-prior-template",
            )
            fresh_path = _paper_path(
                args.fresh_template, paper_dir, label="--fresh-template"
            )
            output_path = _paper_path(args.out, paper_dir, label="--out")
            if output_path in {prior_path, fresh_path}:
                raise SourceRecordManualComplementError(
                    "--out must differ from both template inputs during review seeding"
                )
            fresh_template = _read_json_object(fresh_path)
            canonical_raw = _read_json_object(
                paper_dir / "audit" / "source_record_audit.json"
            )
            runtime = _prepare_manual_complement_runtime(
                canonical_raw, paper=args.paper, paper_dir=paper_dir
            )
            if error := _fresh_template_error(fresh_template, paper=args.paper):
                raise SourceRecordManualComplementError(error)
            if error := current_manual_complement_queue_error(
                fresh_template,
                canonical_raw,
                paper=args.paper,
                paper_dir=paper_dir,
                runtime=runtime,
            ):
                raise SourceRecordManualComplementError(
                    "fresh template cannot guide the current queue: " + error
                )
            seeded, seed_summary = _seed_completed_manual_current_complement_template(
                fresh_template,
                _read_json_object(prior_path),
                paper=args.paper,
            )
            summary = (
                f"{seed_summary['seeded_group_count']} seeded, "
                f"{seed_summary['unresolved_group_count']} unresolved, "
                f"{seed_summary['surplus_prior_group_count']} surplus prior "
                "groups not copied"
            )
            if args.write:
                _write_current_manual_complement_output(
                    output_path,
                    json.dumps(seeded, indent=2, sort_keys=True) + "\n",
                    runtime=runtime,
                    raw_audit=canonical_raw,
                    paper=args.paper,
                    paper_dir=paper_dir,
                )
                print(
                    f"{args.paper}: wrote non-evidence seeded manual-complement template "
                    f"to {output_path} ({summary})"
                )
            else:
                print(
                    f"{args.paper}: completed-template review seeding validates ({summary}); "
                    "rerun with --write"
                )
            return 0
        if args.rebind_completed_prior_template is not None:
            if args.raw_audit is not None:
                raise SourceRecordManualComplementError(
                    "--raw-audit is not used with --rebind-completed-prior-template"
                )
            if args.fresh_template is None or args.out is None:
                raise SourceRecordManualComplementError(
                    "--rebind-completed-prior-template requires --fresh-template and --out"
                )
            prior_path = _paper_path(
                args.rebind_completed_prior_template,
                paper_dir,
                label="--rebind-completed-prior-template",
            )
            fresh_path = _paper_path(
                args.fresh_template, paper_dir, label="--fresh-template"
            )
            output_path = _paper_path(args.out, paper_dir, label="--out")
            if output_path in {prior_path, fresh_path}:
                raise SourceRecordManualComplementError(
                    "--out must differ from both template inputs during completed-template rebind"
                )
            fresh_template = _read_json_object(fresh_path)
            canonical_raw = _read_json_object(
                paper_dir / "audit" / "source_record_audit.json"
            )
            runtime = _prepare_manual_complement_runtime(
                canonical_raw, paper=args.paper, paper_dir=paper_dir
            )
            if error := _fresh_template_error(fresh_template, paper=args.paper):
                raise SourceRecordManualComplementError(error)
            if error := current_manual_complement_queue_error(
                fresh_template,
                canonical_raw,
                paper=args.paper,
                paper_dir=paper_dir,
                runtime=runtime,
            ):
                raise SourceRecordManualComplementError(
                    "fresh template cannot guide the current queue: " + error
                )
            rebound, rebind_summary = _rebind_completed_manual_current_complement_template(
                fresh_template,
                _read_json_object(prior_path),
                paper=args.paper,
            )
            summary = (
                f"{rebind_summary['fresh_group_count']} fresh groups matched to "
                f"{rebind_summary['matched_prior_group_count']} completed-prior groups; "
                f"{rebind_summary['ignored_prior_group_count']} surplus prior groups "
                "were not copied as evidence"
            )
            if args.write:
                _write_current_manual_complement_output(
                    output_path,
                    json.dumps(rebound, indent=2, sort_keys=True) + "\n",
                    runtime=runtime,
                    raw_audit=canonical_raw,
                    paper=args.paper,
                    paper_dir=paper_dir,
                )
                print(
                    f"{args.paper}: wrote rebound completed manual-complement template to "
                    f"{output_path} ({summary})"
                )
            else:
                print(
                    f"{args.paper}: completed-template rebind validates ({summary}); "
                    "rerun with --write"
                )
            return 0
        if args.fresh_template is not None:
            raise SourceRecordManualComplementError(
                "--fresh-template is only valid with a completed-prior template rebind or seed mode"
            )
        raw_path = _paper_path(
            args.raw_audit or paper_dir / "audit" / "source_record_audit.json",
            paper_dir,
            label="--raw-audit",
        )
        raw_audit = _read_json_object(raw_path)
        runtime = _prepare_manual_complement_runtime(
            raw_audit, paper=args.paper, paper_dir=paper_dir
        )
        if args.write_template is not None:
            if args.out is not None or args.write:
                raise SourceRecordManualComplementError(
                    "--write-template cannot be combined with --out or --write"
                )
            template_path = _paper_path(
                args.write_template, paper_dir, label="--write-template"
            )
            template = _manual_current_complement_template(
                raw_audit,
                paper=args.paper,
                paper_dir=paper_dir,
                runtime=runtime,
                _write_boundary_deferral=_MANUAL_COMPLEMENT_WRITE_BOUNDARY_DEFERRAL,
            )
            _write_current_manual_complement_output(
                template_path,
                json.dumps(template, indent=2, sort_keys=True) + "\n",
                runtime=runtime,
                raw_audit=raw_audit,
                paper=args.paper,
                paper_dir=paper_dir,
            )
            print(
                f"{args.paper}: wrote non-evidence manual current-complement template "
                f"to {template_path} ({len(template['manual_current_groups'])} groups)"
            )
            return 0
        if args.completed_template is None or args.out is None:
            raise SourceRecordManualComplementError(
                "--completed-template requires --out"
            )
        completed_path = _paper_path(
            args.completed_template, paper_dir, label="--completed-template"
        )
        output_path = _paper_path(args.out, paper_dir, label="--out")
        completed = _read_json_object(completed_path)
        result = _materialize_manual_current_complement(
            raw_audit,
            completed,
            paper=args.paper,
            paper_dir=paper_dir,
            output_sidecar_path=output_path,
            runtime=runtime,
            _write_boundary_deferral=_MANUAL_COMPLEMENT_WRITE_BOUNDARY_DEFERRAL,
        )
    except SourceRecordManualComplementError as exc:
        print(f"{args.paper}: manual current-complement refused: {exc}", file=sys.stderr)
        return 1
    if args.write:
        _write_current_manual_complement_output(
            output_path,
            json.dumps(result, indent=2, sort_keys=True) + "\n",
            runtime=runtime,
            raw_audit=raw_audit,
            paper=args.paper,
            paper_dir=paper_dir,
        )
        print(
            f"{args.paper}: wrote ordinary current source-record evidence to "
            f"{output_path} ({len(result['items'])} manual groups)"
        )
    else:
        print(
            f"{args.paper}: completed manual current-complement template validates "
            f"({len(result['items'])} manual groups); rerun with --write"
        )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
