"""Typed immutable input transactions shared by paper-audit protocols.

This module owns transaction identity, exact JSON snapshots, deep immutability,
run-scoped memoization, retained operational capabilities, and byte-mutation
detection.  It contains no source-record derivation, Lean discovery, semantic
verdict, or closeout acceptance policy.
"""

from __future__ import annotations

import hashlib
import json
from abc import ABC, abstractmethod
from collections.abc import Callable, Iterable, Mapping
from dataclasses import dataclass, field
from pathlib import Path
from types import MappingProxyType
from typing import Any

from scripts.current_closeout.realization import (
    V11_LEAN_CLAIM_GRAPH_EVIDENCE_LANE,
)
from scripts.immutable_json import freeze_json

LEGACY_SOURCE_RECORD_EVIDENCE_LANE = "legacy_source_record"


@dataclass(frozen=True)
class Finding:
    severity: str
    paper: str
    path: str
    message: str

    def format(self) -> str:
        return f"[{self.severity}] {self.paper} {self.path}: {self.message}"


@dataclass(frozen=True)
class EvidenceJSONSnapshot:
    """One exact JSON input as read for a paper evidence transaction."""

    path: Path
    sha256: str | None
    payload: dict[str, Any] | None
    raw_bytes: bytes | None = None


def load_json_snapshot(path: Path) -> EvidenceJSONSnapshot:
    """Read, hash, parse, and recursively freeze one exact JSON file."""

    try:
        raw = path.read_bytes()
    except OSError:
        return EvidenceJSONSnapshot(path=path, sha256=None, payload=None)
    digest = hashlib.sha256(raw).hexdigest()
    try:
        payload = json.loads(raw)
    except (UnicodeDecodeError, json.JSONDecodeError):
        payload = None
    frozen = freeze_json(payload) if isinstance(payload, dict) else None
    return EvidenceJSONSnapshot(
        path=path,
        sha256=digest,
        payload=frozen,
        raw_bytes=raw,
    )


class EvidenceInputSnapshotTransaction:
    """Acquire every exact paper-audit input once."""

    __slots__ = ("folder", "snapshots_by_path")

    def __init__(self, folder: Path) -> None:
        self.folder = folder
        self.snapshots_by_path: dict[Path, EvidenceJSONSnapshot] = {}

    def snapshot(self, path: Path) -> EvidenceJSONSnapshot:
        """Return the one immutable snapshot for ``path`` in this transaction."""

        try:
            key = path.resolve()
        except (OSError, RuntimeError):
            key = path
        saved = self.snapshots_by_path.get(key)
        if saved is None:
            saved = load_json_snapshot(path)
            self.snapshots_by_path[key] = saved
        return saved

    def canonical_sidecar_path(self, basename: str) -> Path:
        """Freeze and select the organized sidecar or its legacy alias."""

        organized = self.folder / "audit" / basename
        legacy = self.folder / basename
        organized_snapshot = self.snapshot(organized)
        if organized_snapshot.sha256 is not None:
            return organized
        self.snapshot(legacy)
        return legacy

    def noncore_snapshots(
        self,
        core_snapshots: Iterable[EvidenceJSONSnapshot | None],
    ) -> tuple[EvidenceJSONSnapshot, ...]:
        """Return all acquired snapshots except the explicitly named core."""

        core_paths = {
            candidate.path.resolve()
            for candidate in core_snapshots
            if candidate is not None
        }
        return tuple(
            saved
            for key, saved in sorted(
                self.snapshots_by_path.items(), key=lambda item: str(item[0])
            )
            if key not in core_paths
        )


@dataclass(frozen=True)
class LegacySourceRecordInputs:
    """Exact raw source-record inputs acquired only by the legacy lane."""

    audit_snapshot: EvidenceJSONSnapshot
    match_snapshot: EvidenceJSONSnapshot
    audit_path_error: str
    match_path_error: str


@dataclass(frozen=True)
class LegacySourceRecordState:
    """Complete derived state owned exclusively by the legacy raw lane."""

    inputs: LegacySourceRecordInputs
    source_record_identity_error: str
    semantic_contract_revalidation: object | None
    semantic_contract_revalidation_error: str
    corrected_scope_findings: tuple[Finding, ...]
    corrected_scope_current: bool
    corrected_model_field_items: Mapping[str, dict[str, Any]]
    administrative_projection_rebind: object | None
    administrative_projection_rebind_path: Path | None
    administrative_projection_rebind_error: str
    configured_assumption_regularity_context: object | None
    configured_assumption_regularity_context_error: str
    current_source_record_judgments: Mapping[str, dict[str, Any]]
    auxiliary_routing_context: object | None
    auxiliary_routing_context_error: str
    watched_input_digest: str
    source_record_identity_context: object | None = field(
        default=None,
        repr=False,
        compare=False,
    )
    semantic_reuse_authority: object | None = field(
        default=None,
        repr=False,
        compare=False,
    )


class EvidenceRunContextIssuerBinding:
    """Object-identity binding that cannot survive dataclass replacement."""

    __slots__ = (
        "context",
        "current_closeout_pass",
        "current_closeout_pass_authority",
        "current_v11_evidence_integrity_acceptance",
        "current_v11_evidence_integrity_receipt",
        "current_v11_primary_gate_acceptance",
        "primary_closeout_source_record_judgment_receipt",
        "v11_graph_carrier_reuses",
        "v11_review_surface",
        "validation_cache",
        "validation_cache_hits",
        "validation_cache_misses",
    )

    def __init__(self) -> None:
        self.context: EvidenceRunContext | None = None
        self.current_closeout_pass: object | None = None
        self.current_closeout_pass_authority: object | None = None
        self.current_v11_evidence_integrity_acceptance: object | None = None
        self.current_v11_primary_gate_acceptance: object | None = None
        self.current_v11_evidence_integrity_receipt: object | None = None
        self.primary_closeout_source_record_judgment_receipt: object | None = None
        self.validation_cache: dict[tuple[object, ...], object] = {}
        self.validation_cache_hits = 0
        self.validation_cache_misses = 0
        self.v11_graph_carrier_reuses = 0
        self.v11_review_surface: object | None = None


@dataclass(frozen=True)
class EvidenceRunContext(ABC):
    """Common immutable inputs shared by one selected evidence protocol."""

    folder: Path
    status: str
    audit_config_snapshot: EvidenceJSONSnapshot
    status_snapshot: EvidenceJSONSnapshot
    statement_map_snapshot: EvidenceJSONSnapshot
    source_proof_fidelity_snapshot: EvidenceJSONSnapshot | None
    sidecar_snapshots: tuple[EvidenceJSONSnapshot, ...]
    source_proof_fidelity_path_error: str
    _issuer_token: object | None

    @property
    @abstractmethod
    def source_semantic_lane(self) -> str:
        raise NotImplementedError

    @property
    def legacy_source_record_state(self) -> LegacySourceRecordState | None:
        return None

    @property
    def v11_lean_review_graph_snapshot(self) -> EvidenceJSONSnapshot | None:
        return None

    @property
    def issued_by_builder(self) -> bool:
        binding = self._issuer_token
        return (
            isinstance(binding, EvidenceRunContextIssuerBinding)
            and binding.context is self
        )

    @property
    def v11_lean_claim_graph_selected(self) -> bool:
        return self.source_semantic_lane == V11_LEAN_CLAIM_GRAPH_EVIDENCE_LANE

    @property
    def status_payload(self) -> dict[str, Any]:
        return self.status_snapshot.payload or {}

    def require_legacy_source_record_state(self) -> LegacySourceRecordState:
        state = self.legacy_source_record_state
        if state is None:
            raise ValueError(
                "selected v11 transaction has no legacy source-record state"
            )
        return state

    @property
    def corrected_scope_findings(self) -> tuple[Finding, ...]:
        state = self.legacy_source_record_state
        return state.corrected_scope_findings if state is not None else ()

    @property
    def corrected_scope_current(self) -> bool:
        state = self.legacy_source_record_state
        return state.corrected_scope_current if state is not None else False

    @property
    def statement_map(self) -> dict[str, Any] | None:
        return self.statement_map_snapshot.payload

    @property
    def paper_statement_map_sha256(self) -> str:
        return self.statement_map_snapshot.sha256 or ""

    @property
    def source_proof_fidelity(self) -> dict[str, Any] | None:
        snapshot = self.source_proof_fidelity_snapshot
        return snapshot.payload if snapshot is not None else None

    @property
    def input_snapshots(self) -> tuple[EvidenceJSONSnapshot, ...]:
        snapshots = (
            self.audit_config_snapshot,
            self.status_snapshot,
            self.statement_map_snapshot,
        )
        legacy_state = self.legacy_source_record_state
        if legacy_state is not None:
            snapshots += (
                legacy_state.inputs.audit_snapshot,
                legacy_state.inputs.match_snapshot,
            )
        if self.source_proof_fidelity_snapshot is not None:
            snapshots += (self.source_proof_fidelity_snapshot,)
        if self.v11_lean_review_graph_snapshot is not None:
            snapshots += (self.v11_lean_review_graph_snapshot,)
        return snapshots + self.sidecar_snapshots

    @property
    def v11_lean_review_graph_payload(self) -> dict[str, Any] | None:
        snapshot = self.v11_lean_review_graph_snapshot
        return snapshot.payload if snapshot is not None else None

    def json_snapshot(self, path: Path) -> EvidenceJSONSnapshot | None:
        try:
            target = path.resolve()
        except (OSError, RuntimeError):
            return None
        for snapshot in self.input_snapshots:
            try:
                if snapshot.path.resolve() == target:
                    return snapshot
            except (OSError, RuntimeError):
                continue
        return None

    def json_payload(self, path: Path) -> dict[str, Any] | None:
        snapshot = self.json_snapshot(path)
        return snapshot.payload if snapshot is not None else None

    def file_bytes_override(self) -> Mapping[Path, bytes | None]:
        return MappingProxyType(
            {
                snapshot.path.resolve(): snapshot.raw_bytes
                for snapshot in self.input_snapshots
            }
        )

    def canonical_sidecar_path(self, basename: str) -> Path:
        organized = self.folder / "audit" / basename
        if self.v11_lean_claim_graph_selected:
            return organized
        organized_snapshot = self.json_snapshot(organized)
        if organized_snapshot is not None and organized_snapshot.sha256 is not None:
            return organized
        return self.folder / basename

    def runtime_cache_diagnostics(self) -> Mapping[str, int]:
        binding = self._issuer_token
        if (
            not self.issued_by_builder
            or not isinstance(binding, EvidenceRunContextIssuerBinding)
        ):
            return MappingProxyType({})
        return MappingProxyType(
            {
                "validation_cache_hits": binding.validation_cache_hits,
                "validation_cache_misses": binding.validation_cache_misses,
                "validation_cache_entries": len(binding.validation_cache),
                "v11_graph_carrier_reuses": binding.v11_graph_carrier_reuses,
            }
        )

    def retained_v11_review_surface(self) -> object | None:
        binding = self._issuer_token
        if (
            not self.issued_by_builder
            or not isinstance(binding, EvidenceRunContextIssuerBinding)
            or not self.v11_lean_claim_graph_selected
        ):
            return None
        return binding.v11_review_surface

    def retain_v11_review_surface(self, surface: object) -> None:
        """Retain exactly one Lean review surface in this issued transaction."""

        binding = self._issuer_token
        if (
            not self.issued_by_builder
            or not isinstance(binding, EvidenceRunContextIssuerBinding)
            or not self.v11_lean_claim_graph_selected
        ):
            raise ValueError(
                "v11 Lean review surface requires its exact issued transaction"
            )
        retained = binding.v11_review_surface
        if retained is not None and retained is not surface:
            raise ValueError(
                "exact evidence transaction cannot retain multiple v11 Lean graphs"
            )
        binding.v11_review_surface = surface

    def record_v11_graph_carrier_reuse(self, *, carrier_reused: bool) -> None:
        """Record reuse only on this exact current transaction capability."""

        if not carrier_reused or not self.v11_lean_claim_graph_selected:
            return
        binding = self._issuer_token
        if self.issued_by_builder and isinstance(
            binding, EvidenceRunContextIssuerBinding
        ):
            binding.v11_graph_carrier_reuses += 1

    def changed_input_paths(self) -> tuple[Path, ...]:
        """Return exact transaction files whose bytes changed after acquisition."""

        return tuple(
            snapshot.path
            for snapshot in self.input_snapshots
            if path_content_sha256(snapshot.path) != snapshot.sha256
        )


@dataclass(frozen=True)
class V11EvidenceRunContext(EvidenceRunContext):
    """Current Lean-graph transaction with no representable legacy payload."""

    lean_review_graph_snapshot: EvidenceJSONSnapshot | None = None

    @property
    def source_semantic_lane(self) -> str:
        return V11_LEAN_CLAIM_GRAPH_EVIDENCE_LANE

    @property
    def v11_lean_review_graph_snapshot(self) -> EvidenceJSONSnapshot | None:
        return self.lean_review_graph_snapshot


@dataclass(frozen=True)
class LegacyEvidenceRunContext(EvidenceRunContext):
    """Historical raw-source transaction with its complete derived state."""

    legacy_state: LegacySourceRecordState

    @property
    def source_semantic_lane(self) -> str:
        return LEGACY_SOURCE_RECORD_EVIDENCE_LANE

    @property
    def legacy_source_record_state(self) -> LegacySourceRecordState:
        return self.legacy_state


@dataclass(frozen=True)
class CommonEvidenceRunContextInputs:
    """Protocol-neutral output of one immutable snapshot acquisition."""

    folder: Path
    status: str
    audit_config_snapshot: EvidenceJSONSnapshot
    status_snapshot: EvidenceJSONSnapshot
    statement_map_snapshot: EvidenceJSONSnapshot
    source_proof_fidelity_snapshot: EvidenceJSONSnapshot | None
    sidecar_snapshots: tuple[EvidenceJSONSnapshot, ...]
    source_proof_fidelity_path_error: str

    def _kwargs(self, issuer: EvidenceRunContextIssuerBinding) -> dict[str, Any]:
        return {
            "folder": self.folder.resolve(),
            "status": self.status,
            "audit_config_snapshot": self.audit_config_snapshot,
            "status_snapshot": self.status_snapshot,
            "statement_map_snapshot": self.statement_map_snapshot,
            "source_proof_fidelity_snapshot": self.source_proof_fidelity_snapshot,
            "sidecar_snapshots": self.sidecar_snapshots,
            "source_proof_fidelity_path_error": (
                self.source_proof_fidelity_path_error
            ),
            "_issuer_token": issuer,
        }

    def issue_v11(
        self,
        lean_review_graph_snapshot: EvidenceJSONSnapshot | None,
    ) -> V11EvidenceRunContext:
        issuer = EvidenceRunContextIssuerBinding()
        context = V11EvidenceRunContext(
            **self._kwargs(issuer),
            lean_review_graph_snapshot=lean_review_graph_snapshot,
        )
        issuer.context = context
        return context

    def issue_legacy(
        self,
        legacy_state: LegacySourceRecordState,
    ) -> LegacyEvidenceRunContext:
        issuer = EvidenceRunContextIssuerBinding()
        context = LegacyEvidenceRunContext(
            **self._kwargs(issuer),
            legacy_state=legacy_state,
        )
        issuer.context = context
        return context


class PrimaryCloseoutSourceRecordJudgmentReceipt:
    """Opaque in-process proof that the primary gate covered source judgments."""

    __slots__ = (
        "context",
        "source_semantic_lane",
        "statement_map_snapshot",
        "status_snapshot",
    )

    def __init__(self, context: EvidenceRunContext) -> None:
        self.context = context
        self.status_snapshot = context.status_snapshot
        self.statement_map_snapshot = context.statement_map_snapshot
        self.source_semantic_lane = context.source_semantic_lane


class CurrentV11EvidenceIntegrityReceipt:
    """Opaque in-process proof that the exact current evidence stage passed."""

    __slots__ = (
        "context",
        "source_proof_fidelity_snapshot",
        "statement_map_snapshot",
        "status_snapshot",
    )

    def __init__(self, context: V11EvidenceRunContext) -> None:
        self.context = context
        self.status_snapshot = context.status_snapshot
        self.statement_map_snapshot = context.statement_map_snapshot
        self.source_proof_fidelity_snapshot = (
            context.source_proof_fidelity_snapshot
        )


def issue_primary_closeout_source_record_judgment_receipt(
    context: object,
) -> bool:
    """Publish the historical raw-lane primary handoff.

    Current v11 acceptance is verdict-shaped and is issued only by
    ``current_closeout.primary_gate_transaction``.  Keeping this older bridge
    legacy-only prevents an in-process caller from manufacturing current
    semantic credit merely by calling a staging method.
    """

    if not isinstance(context, LegacyEvidenceRunContext) or not context.issued_by_builder:
        return False
    binding = context._issuer_token
    if (
        not isinstance(binding, EvidenceRunContextIssuerBinding)
        or binding.context is not context
    ):
        return False
    binding.primary_closeout_source_record_judgment_receipt = (
        PrimaryCloseoutSourceRecordJudgmentReceipt(context)
    )
    return True


def has_current_primary_closeout_source_record_judgment_receipt(
    context: object,
) -> bool:
    """Accept only the historical raw-lane handoff for ``context``."""

    if not isinstance(context, LegacyEvidenceRunContext) or not context.issued_by_builder:
        return False
    binding = context._issuer_token
    if (
        not isinstance(binding, EvidenceRunContextIssuerBinding)
        or binding.context is not context
    ):
        return False
    receipt = binding.primary_closeout_source_record_judgment_receipt
    return bool(
        isinstance(receipt, PrimaryCloseoutSourceRecordJudgmentReceipt)
        and receipt.context is context
        and receipt.status_snapshot is context.status_snapshot
        and receipt.statement_map_snapshot is context.statement_map_snapshot
        and receipt.source_semantic_lane == context.source_semantic_lane
    )


def issue_current_v11_evidence_integrity_receipt(context: object) -> bool:
    """Retired call-shaped issuer retained as a nonaccepting compatibility API."""

    del context
    return False


def has_current_v11_evidence_integrity_receipt(context: object) -> bool:
    """Retired call-shaped validator; current acceptance lives with the gate."""

    del context
    return False


_VALIDATION_CACHE_MISS = object()


def run_scoped_cached_value(
    context: EvidenceRunContext | None,
    *,
    folder: Path,
    key: tuple[object, ...],
    compute: Callable[[], Any],
) -> Any:
    """Evaluate one pure input-bound operation once per exact transaction."""

    if (
        not isinstance(context, EvidenceRunContext)
        or not context.issued_by_builder
        or context.folder != folder.resolve()
    ):
        return compute()
    binding = context._issuer_token
    if not isinstance(binding, EvidenceRunContextIssuerBinding):
        return compute()
    cached = binding.validation_cache.get(key, _VALIDATION_CACHE_MISS)
    if cached is _VALIDATION_CACHE_MISS:
        cached = compute()
        binding.validation_cache[key] = cached
        binding.validation_cache_misses += 1
    else:
        binding.validation_cache_hits += 1
    return cached


def run_scoped_validation_findings(
    context: EvidenceRunContext | None,
    *,
    folder: Path,
    status: str,
    require_source_bytes: bool,
    validator: str,
    compute: Callable[[], list[Finding]],
) -> list[Finding]:
    """Evaluate one strict findings validator once per exact transaction."""

    cached = run_scoped_cached_value(
        context,
        folder=folder,
        key=(
            "findings",
            validator,
            str(status).strip().lower(),
            bool(require_source_bytes),
        ),
        compute=lambda: tuple(compute()),
    )
    if not isinstance(cached, tuple) or any(
        not isinstance(item, Finding) for item in cached
    ):
        raise TypeError(f"{validator} returned a non-Finding result")
    return list(cached)


def path_content_sha256(path: Path) -> str | None:
    """Return only a file's exact byte digest; never parse it."""

    try:
        return hashlib.sha256(path.read_bytes()).hexdigest()
    except OSError:
        return None
