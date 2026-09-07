#!/usr/bin/env python3
"""Replay authenticated source-record overlay lanes as a typed union.

An overlay loader is the authority for its own historical transport.  This
module deliberately does not compare source keys, declaration names, binder
names, or function names.  It invokes each registered loader, requires its
private in-memory capability on every returned item, and exposes the resulting
current response slots as named *transport lanes*.  Consumers can then choose
their collision policy explicitly instead of accidentally inheriting dict
merge precedence.

The registry is loaded lazily because a few legacy transports import the
current-revalidation validator while replaying their own receipts.  Callers
therefore import this module only after their shared v10 surface is available.
"""

from __future__ import annotations

from dataclasses import dataclass, field
from importlib import import_module
from pathlib import Path
from typing import Any, Callable, Iterable, Mapping

try:
    from scripts.source_record_archived_transports import (
        archived_source_record_transport_artifacts,
    )
    from scripts.source_record_overlay_protocol import (
        SOURCE_RECORD_OVERLAY_PROTOCOL_BY_LABEL,
        SOURCE_RECORD_OVERLAY_PROTOCOLS,
        serialized_source_record_overlay_labels,
        source_record_overlay_labels_with_artifacts,
    )
except ModuleNotFoundError:  # pragma: no cover - direct-script fallback.
    from source_record_archived_transports import (
        archived_source_record_transport_artifacts,
    )
    from source_record_overlay_protocol import (
        SOURCE_RECORD_OVERLAY_PROTOCOL_BY_LABEL,
        SOURCE_RECORD_OVERLAY_PROTOCOLS,
        serialized_source_record_overlay_labels,
        source_record_overlay_labels_with_artifacts,
    )


class SourceRecordAuthenticatedOverlayUnionError(ValueError):
    """Raised when a purported loader-authenticated overlay is malformed."""


_LOADED_LANE_SENTINEL = object()


@dataclass(frozen=True)
class AuthenticatedCurrentOverlayLane:
    """One loader-owned set of current response slots.

    ``items`` retains the loader-private dict subclass.  Copying it to an
    ordinary ``dict`` is intentionally left to consumers that no longer need
    the capability; the registry itself uses the capability to reject a
    deserialized provenance marker.
    """

    label: str
    items: dict[str, Mapping[str, Any]]
    _loader_token: object = field(repr=False, compare=False)
    _is_loaded: Callable[[object], bool] = field(repr=False, compare=False)
    _copy_loaded: Callable[
        [Mapping[str, Any], Mapping[str, Any] | None], dict[str, Any]
    ] = field(repr=False, compare=False)
    _issued_items: list[Mapping[str, Any]] = field(repr=False, compare=False)


def _overlay_modules(lane_labels: Iterable[str] | None = None) -> dict[str, Any]:
    """Import only the transport modules selected for current replay."""

    selected = (
        set(SOURCE_RECORD_OVERLAY_PROTOCOL_BY_LABEL)
        if lane_labels is None
        else {str(label or "").strip() for label in lane_labels}
    )
    modules: dict[str, Any] = {}
    for label in selected:
        protocol = SOURCE_RECORD_OVERLAY_PROTOCOL_BY_LABEL[label]
        qualified = f"scripts.{protocol.module_name}"
        try:
            module = import_module(qualified)
        except ModuleNotFoundError as exc:  # pragma: no cover - direct-script fallback.
            # Fall back only when the package path itself is unavailable.  A
            # missing transitive dependency remains a real loader failure.
            if exc.name not in {"scripts", qualified}:
                raise
            module = import_module(protocol.module_name)
        modules[label] = module
    return modules


def _evidence_module() -> Any:
    """Load the neutral current-identity issuer only when a lane needs it."""

    try:
        from scripts import audit_evidence_integrity as evidence
    except ModuleNotFoundError:  # pragma: no cover - direct-script fallback.
        import audit_evidence_integrity as evidence
    return evidence


def _validated_lane_items(
    label: str,
    loaded: object,
    *,
    is_loaded: Callable[[object], bool],
) -> dict[str, Mapping[str, Any]]:
    """Validate a loader result without accepting serialized provenance.

    A response key is only an address in the already-generated current group
    ledger.  It is not used here, or by callers, to infer a semantic match.
    """

    if not isinstance(loaded, Mapping):
        raise SourceRecordAuthenticatedOverlayUnionError(
            f"authenticated {label} overlay loader returned a non-mapping result"
        )
    out: dict[str, Mapping[str, Any]] = {}
    for raw_key, value in loaded.items():
        key = str(raw_key or "").strip()
        if not key or key in out:
            raise SourceRecordAuthenticatedOverlayUnionError(
                f"authenticated {label} overlay loader returned an empty or duplicate current slot"
            )
        if not isinstance(value, Mapping) or not is_loaded(value):
            raise SourceRecordAuthenticatedOverlayUnionError(
                f"authenticated {label} overlay loader returned an item without its private capability"
            )
        out[key] = value
    return out


def load_authenticated_current_overlay_lanes(
    paper_dir: Path,
    paper: str,
    current_raw_audit: Mapping[str, Any],
    *,
    lane_labels: Iterable[str] | None = None,
    differential_overlay_path: Path | None = None,
    differential_current_raw_audit_path: Path | None = None,
    differential_current_raw_audit_provenance_path: Path | None = None,
    source_record_identity_context: object | None = None,
) -> tuple[AuthenticatedCurrentOverlayLane, ...]:
    """Replay registered current transports and retain their private tokens.

    ``lane_labels`` is an explicit selection of registry lanes, not a pattern
    over paths, declaration names, or response keys.  Empty lanes are retained
    so a persisted consumer can bind the complete current transport surface,
    including the fact that a registered lane supplied no current slots.
    """

    archived_artifacts = archived_source_record_transport_artifacts(paper_dir)
    if archived_artifacts:
        rendered = ", ".join(str(path) for path in archived_artifacts)
        raise SourceRecordAuthenticatedOverlayUnionError(
            "retired source-record transport artifact requires fresh current evidence: "
            + rendered
        )
    known_labels = set(SOURCE_RECORD_OVERLAY_PROTOCOL_BY_LABEL)
    artifact_labels = set(source_record_overlay_labels_with_artifacts(paper_dir))
    default_labels = tuple(
        protocol.label
        for protocol in SOURCE_RECORD_OVERLAY_PROTOCOLS
        if protocol.replay_without_artifact or protocol.label in artifact_labels
    )
    requested = (
        default_labels
        if lane_labels is None
        else tuple(str(label or "").strip() for label in lane_labels)
    )
    if (
        not requested
        or any(not label or label not in known_labels for label in requested)
        or any(
            not SOURCE_RECORD_OVERLAY_PROTOCOL_BY_LABEL[label].replay_without_artifact
            and label not in artifact_labels
            for label in requested
            if label in known_labels
        )
    ):
        raise SourceRecordAuthenticatedOverlayUnionError(
            "authenticated overlay lane selection names an unknown, absent, or empty lane"
        )
    if len(set(requested)) != len(requested):
        raise SourceRecordAuthenticatedOverlayUnionError(
            "authenticated overlay lane selection repeats a lane"
        )
    modules = _overlay_modules(requested)
    selected = set(requested)
    identity_context = source_record_identity_context
    identity_context_prepared = False

    def current_identity_context() -> object | None:
        """Issue or revalidate one opaque identity for the lanes that need it."""

        nonlocal identity_context, identity_context_prepared
        if identity_context_prepared:
            return identity_context
        evidence = _evidence_module()
        if identity_context is None:
            identity_context = evidence.prepare_current_source_record_identity_context(
                paper_dir, paper, current_raw_audit
            )
        else:
            error = evidence.current_source_record_identity_context_error(
                identity_context,
                paper_dir=paper_dir,
                paper=paper,
                current_raw_audit=current_raw_audit,
            )
            if error:
                raise SourceRecordAuthenticatedOverlayUnionError(
                    "authenticated overlay identity context is invalid: " + error
                )
        identity_context_prepared = True
        return identity_context

    lanes: list[AuthenticatedCurrentOverlayLane] = []
    for protocol in SOURCE_RECORD_OVERLAY_PROTOCOLS:
        label = protocol.label
        if label not in selected:
            continue
        module = modules[label]
        loader = getattr(module, protocol.loader_function)
        try:
            if label == "semantic_rebind":
                context = current_identity_context()
                loaded = (
                    {}
                    if context is None
                    else loader(
                        paper_dir,
                        paper,
                        current_raw_audit,
                        source_record_identity_context=context,
                    )
                )
            elif label == "differential":
                loaded = loader(
                    paper_dir,
                    paper,
                    current_raw_audit,
                    path=differential_overlay_path,
                    current_raw_audit_path=differential_current_raw_audit_path,
                    current_raw_audit_provenance_path=(
                        differential_current_raw_audit_provenance_path
                    ),
                )
            else:
                loaded = loader(paper_dir, paper, current_raw_audit)
        except Exception as exc:  # noqa: BLE001 - fail closed across transport boundaries.
            raise SourceRecordAuthenticatedOverlayUnionError(
                f"authenticated {label} overlay loader raised {type(exc).__name__}: {exc}"
            ) from exc
        is_loaded = getattr(module, protocol.capability_function)
        copy_loaded = getattr(module, protocol.copy_function)
        validated_items = _validated_lane_items(label, loaded, is_loaded=is_loaded)
        lanes.append(
            AuthenticatedCurrentOverlayLane(
                label=label,
                items=validated_items,
                _loader_token=_LOADED_LANE_SENTINEL,
                _is_loaded=is_loaded,
                _copy_loaded=copy_loaded,
                _issued_items=list(validated_items.values()),
            )
        )
    return tuple(lanes)


def _authenticated_lane_error(lane: object) -> str:
    if not isinstance(lane, AuthenticatedCurrentOverlayLane):
        return "authenticated overlay operation received an untyped lane"
    if lane._loader_token is not _LOADED_LANE_SENTINEL:
        return "authenticated overlay operation received a lane without loader authority"
    if lane.label not in SOURCE_RECORD_OVERLAY_PROTOCOL_BY_LABEL:
        return "authenticated overlay operation received a lane with an unknown label"
    return ""


def authenticated_current_overlay_item(
    lane: AuthenticatedCurrentOverlayLane,
    value: object,
) -> bool:
    """Whether ``value`` is an exact item issued in ``lane``'s replay."""

    if _authenticated_lane_error(lane):
        return False
    return bool(
        any(candidate is value for candidate in lane._issued_items)
        and lane._is_loaded(value)
    )


def copy_authenticated_current_overlay_item(
    lane: AuthenticatedCurrentOverlayLane,
    value: Mapping[str, Any],
    updates: Mapping[str, Any] | None = None,
) -> dict[str, Any]:
    """Normalize one exact lane item while retaining its private capability."""

    error = _authenticated_lane_error(lane)
    if error:
        raise SourceRecordAuthenticatedOverlayUnionError(error)
    if not authenticated_current_overlay_item(lane, value):
        raise SourceRecordAuthenticatedOverlayUnionError(
            f"authenticated {lane.label} overlay copy received an item outside its loaded lane"
        )
    copied = lane._copy_loaded(value, updates)
    if not lane._is_loaded(copied):
        raise SourceRecordAuthenticatedOverlayUnionError(
            f"authenticated {lane.label} overlay copy discarded its private capability"
        )
    lane._issued_items.append(copied)
    return copied


def authenticated_current_overlay_lane_for_item(
    lanes: Iterable[AuthenticatedCurrentOverlayLane],
    value: object,
) -> AuthenticatedCurrentOverlayLane | None:
    """Return the unique loader lane that issued ``value``."""

    matches = [
        lane for lane in lanes if authenticated_current_overlay_item(lane, value)
    ]
    if len(matches) > 1:
        raise SourceRecordAuthenticatedOverlayUnionError(
            "authenticated overlay item is owned by more than one loader lane"
        )
    return matches[0] if matches else None


def copy_authenticated_or_plain_current_item(
    lanes: Iterable[AuthenticatedCurrentOverlayLane],
    value: Mapping[str, Any],
    updates: Mapping[str, Any] | None = None,
) -> dict[str, Any]:
    """Copy a current response without trusting a serialized overlay marker."""

    retained_lanes = tuple(lanes)
    lane = authenticated_current_overlay_lane_for_item(retained_lanes, value)
    if lane is not None:
        return copy_authenticated_current_overlay_item(lane, value, updates)
    if serialized_source_record_overlay_labels(value):
        raise SourceRecordAuthenticatedOverlayUnionError(
            "serialized overlay provenance has no loader-owned current lane"
        )
    copied = dict(value)
    if updates is not None:
        copied.update(updates)
    return copied


def loader_authenticated_current_overlay_label(value: object) -> str | None:
    """Return the private-capability transport label for an in-memory item.

    This is a process-local capability check only. It does not establish that
    the item is current for a paper; that remains the loader transaction's
    responsibility. It exists for downstream consumers that must preserve the
    capability after the current lanes have already been composed.
    """

    labels = serialized_source_record_overlay_labels(value)
    if len(labels) != 1:
        return None
    label = labels[0]
    protocol = SOURCE_RECORD_OVERLAY_PROTOCOL_BY_LABEL[label]
    module = _overlay_modules((label,))[label]
    capability = getattr(module, protocol.capability_function)
    return label if capability(value) else None


def copy_loader_authenticated_or_plain_current_item(
    value: Mapping[str, Any],
    updates: Mapping[str, Any] | None = None,
) -> dict[str, Any]:
    """Preserve a valid loader capability or copy an ordinary response.

    A serialized overlay marker without its loader's private token is rejected
    rather than silently normalized into ordinary evidence.
    """

    label = loader_authenticated_current_overlay_label(value)
    if label is not None:
        protocol = SOURCE_RECORD_OVERLAY_PROTOCOL_BY_LABEL[label]
        module = _overlay_modules((label,))[label]
        copied = getattr(module, protocol.copy_function)(value, updates)
        if loader_authenticated_current_overlay_label(copied) != label:
            raise SourceRecordAuthenticatedOverlayUnionError(
                f"authenticated {label} overlay copy discarded its private capability"
            )
        return copied
    if serialized_source_record_overlay_labels(value):
        raise SourceRecordAuthenticatedOverlayUnionError(
            "serialized overlay provenance has no loader-owned current capability"
        )
    copied = dict(value)
    if updates is not None:
        copied.update(updates)
    return copied


def strict_authenticated_current_overlay_union(
    lanes: Iterable[AuthenticatedCurrentOverlayLane],
) -> dict[str, Mapping[str, Any]]:
    """Return a union only when every current slot has one transport owner.

    Normal evidence consumption has a documented precedence order.  A manual
    complement must instead know exactly why each omitted current group is
    omitted, so a cross-lane collision is a deterministic error rather than
    an overwrite.
    """

    out: dict[str, Mapping[str, Any]] = {}
    owners: dict[str, str] = {}
    for lane in lanes:
        if error := _authenticated_lane_error(lane):
            raise SourceRecordAuthenticatedOverlayUnionError(error)
        for key, value in lane.items.items():
            if not authenticated_current_overlay_item(lane, value):
                raise SourceRecordAuthenticatedOverlayUnionError(
                    f"authenticated {lane.label} overlay union contains an item outside its loaded lane"
                )
            if key in out:
                raise SourceRecordAuthenticatedOverlayUnionError(
                    "authenticated overlay lanes overlap at current semantic group "
                    f"`{key}` ({owners[key]} and {lane.label})"
                )
            out[key] = value
            owners[key] = lane.label
    return out
