#!/usr/bin/env python3
"""Fail-closed reissue of v10 statement-semantic receipts.

This is deliberately not another semantic-audit generator.  It helps a
reviewer replace receipts after a source-map or route repair without turning
old prose into new evidence:

* ``--emit-template`` writes a non-evidence, byte-pinned work queue.  It
  contains content identities for the current cache/manifest surface and for
  prior payload groups, but no judgment body.
* ``--emit-action-scaffold`` additionally classifies the content identities
  into conservative reuse, fresh-review, and retirement candidates.  It is a
  planning aid, never a partially materialized audit: fresh bodies and
  retirement reasons are deliberately absent, and ambiguous semantic classes
  are left unresolved rather than guessed.
* A reviewer supplies an explicit plan with ``fresh``, ``reuse``, and
  ``retire`` actions.  A fresh action must contain a complete reviewer-authored
  semantic ledger.  A reuse action is accepted only when the prior ledger is
  already valid against the exact current source route and Lean manifest.
* Every prior payload group must be classified.  Retirement is allowed only
  after a semantic anti-join against every current cache class; it cannot
  delete a receipt merely because a storage key or declaration spelling moved.
* ``--write`` archives the exact raw bytes of the prior sidecar before replacing
  it.  Both files are written atomically.  The default materialization is a
  dry run.
* Re-running a completed plan is a no-op only when the current sidecar and,
  where needed, the exact archive byte-match that plan's deterministic output.
  A stale plan with altered evidence still fails closed.

Storage keys, source-map keys, and Lean declaration names are navigation aids
only.  The matching identity is the elaborated Lean signature digest plus the
source-target and Lean-to-TeX statement digests.  This makes rekeys harmless
while refusing changed mathematical content, changed source routes, and
ambiguous duplicate evidence.
"""

from __future__ import annotations

import argparse
import base64
import copy
import hashlib
import json
import os
import re
import sys
import tempfile
from dataclasses import dataclass
from pathlib import Path, PurePosixPath
from typing import Any, Callable, Iterable, Mapping, Sequence


ROOT = Path(__file__).resolve().parents[1]
if str(ROOT / "scripts") not in sys.path:
    sys.path.insert(0, str(ROOT / "scripts"))

import review_dashboard  # noqa: E402
import historical_statement_manifest_replay as historical_manifest_replay  # noqa: E402
import historical_statement_manifest_runner as historical_manifest_runner  # noqa: E402
import historical_manifest_store_recovery as historical_manifest_store_recovery  # noqa: E402
try:  # Supports direct-script execution and package imports.
    from scripts import lean_import_closure
    from scripts.source_coverage_scope import source_map_cache_semantic_sha256
    from scripts.source_record_integrity import (
        source_record_audit_receipt_error,
        source_record_target_route_error,
    )
except ModuleNotFoundError:  # pragma: no cover - direct script fallback.
    import lean_import_closure
    from source_coverage_scope import source_map_cache_semantic_sha256
    from source_record_integrity import (
        source_record_audit_receipt_error,
        source_record_target_route_error,
    )


REISSUE_SCHEMA = 1
TEMPLATE_KIND = "statement_receipt_reissue_template"
ACTION_SCAFFOLD_KIND = "statement_receipt_reissue_action_scaffold"
PLAN_KIND = "statement_receipt_reissue_plan"
ARCHIVE_KIND = "statement_receipt_reissue_archive"
POLICY_VERSION = "statement-receipt-reissue-v1-content-pinned"
HISTORICAL_REPLAY_ACTION = "historical_replay_reuse"
HISTORICAL_REPLAY_PLAN_FIELD = "historical_statement_manifest_replay"
HISTORICAL_REPLAY_PROVENANCE_FIELD = "historical_statement_manifest_replay_v1"
HISTORICAL_REPLAY_PROVENANCE_SCHEMA = 1
HISTORICAL_REPLAY_PROVENANCE_KIND = (
    "statement_receipt_historical_manifest_replay_transport"
)
HISTORICAL_REPLAY_PROVENANCE_POLICY_VERSION = (
    "statement-receipt-historical-manifest-replay-transport-v1"
)
HISTORICAL_REPLAY_RECOVERED_STORE_PROVENANCE_POLICY_VERSION = (
    "statement-receipt-historical-manifest-replay-transport-v2-recovered-store"
)
HISTORICAL_REPLAY_RECOVERED_STORE_FIELD = "recovered_manifest_store"
HISTORICAL_REPLAY_RECOVERED_STORE_FIELDS = frozenset(
    {
        "recovery_receipt_path",
        "recovery_receipt_bytes_sha256",
        "authority_path",
        "authority_bytes_sha256",
        "carrier_compressed_path",
        "carrier_compressed_bytes_sha256",
    }
)
NON_EVIDENCE_FIELDS = (
    "non_evidence_scaffold",
    "must_not_be_written_to_repository_sidecar",
)
_CANDIDATE_MARKERS = frozenset(
    {
        "candidate_only",
        "is_candidate",
        "draft",
        "is_draft",
        "draft_only",
        "proposal_only",
        "not_evidence",
        *NON_EVIDENCE_FIELDS,
    }
)
_FRESH_GENERATED_FIELDS = frozenset(
    {
        "schema",
        "paper",
        "prompt_version",
        "validator",
        "validator_type",
        "validated_at",
        "lean_statement_sha256",
        "lean_signature_sha256",
        "paper_statement_sha256",
        "tex_statement_sha256",
        "semantic_reuse_v1",
        HISTORICAL_REPLAY_PROVENANCE_FIELD,
    }
)
_SHA256_RE = re.compile(r"^[0-9a-f]{64}$")
_EMPTY_STATEMENT_SHA256 = review_dashboard.statement_digest("")


class StatementReceiptReissueError(ValueError):
    """Raised when a reissue plan cannot establish current evidence."""


def statement_receipt_review_rows(
    rows: Iterable[review_dashboard.ReviewItem],
) -> list[review_dashboard.ReviewItem]:
    """Select paper claims; source-model assumptions have a separate review lane."""

    return [item for item in rows if not item.is_assumption]


HistoricalManifestReplayRecipeVerifier = Callable[[Mapping[str, object]], str | None]
HistoricalManifestReplayCurrentClosureAuthorityVerifier = Callable[
    ["CurrentReceiptSurface", Mapping[str, object]],
    tuple[dict[str, Any], bytes, str],
]


def _canonical_bytes(value: object) -> bytes:
    return json.dumps(
        value,
        ensure_ascii=False,
        sort_keys=True,
        separators=(",", ":"),
    ).encode("utf-8")


def _digest(value: object) -> str:
    return hashlib.sha256(_canonical_bytes(value)).hexdigest()


def _bytes_sha256(value: bytes) -> str:
    return hashlib.sha256(value).hexdigest()


def _sha256(value: object) -> str:
    text = str(value or "").strip().lower()
    return text if _SHA256_RE.fullmatch(text) else ""


def _required_sha256(value: object, *, label: str) -> str:
    digest = _sha256(value)
    if not digest:
        raise StatementReceiptReissueError(f"{label} must be a SHA-256 digest")
    return digest


def _required_text(value: object, *, label: str) -> str:
    text = str(value or "").strip()
    if not text:
        raise StatementReceiptReissueError(f"{label} must be nonempty")
    return text


def _target_identity(
    *,
    lean_signature_sha256: str,
    paper_statement_sha256: str,
    tex_statement_sha256: str,
) -> dict[str, str]:
    return {
        "lean_signature_sha256": lean_signature_sha256,
        "paper_statement_sha256": paper_statement_sha256,
        "tex_statement_sha256": tex_statement_sha256,
    }


def semantic_target_sha256(identity: Mapping[str, Any]) -> str:
    """Return the content address of a complete statement receipt target."""

    return _digest(
        {
            "schema": REISSUE_SCHEMA,
            "identity": {
                field: _required_sha256(identity.get(field), label=field)
                for field in (
                    "lean_signature_sha256",
                    "paper_statement_sha256",
                    "tex_statement_sha256",
                )
            },
        }
    )


def semantic_class_sha256(
    *, lean_signature_sha256: str, tex_statement_sha256: str
) -> str:
    """Return the source-target-independent current cache class address.

    This intentionally excludes a source-map key, declaration name, and the
    storage key.  The class is used for conservative orphan retirement: if the
    same Lean proposition and translated statement still occur anywhere in the
    current cache, an old receipt needs an explicit fresh supersession rather
    than an automatic delete.
    """

    return _digest(
        {
            "schema": REISSUE_SCHEMA,
            "lean_signature_sha256": _required_sha256(
                lean_signature_sha256, label="lean_signature_sha256"
            ),
            "tex_statement_sha256": _required_sha256(
                tex_statement_sha256, label="tex_statement_sha256"
            ),
        }
    )


@dataclass(frozen=True)
class CurrentReceiptTarget:
    """One current semantic receipt target, addressed without a row name."""

    lean_signature_sha256: str
    paper_statement_sha256: str
    tex_statement_sha256: str
    lean_statement_sha256: str
    manifest: Mapping[str, Any]

    @property
    def identity(self) -> dict[str, str]:
        return _target_identity(
            lean_signature_sha256=self.lean_signature_sha256,
            paper_statement_sha256=self.paper_statement_sha256,
            tex_statement_sha256=self.tex_statement_sha256,
        )

    @property
    def semantic_target_sha256(self) -> str:
        return semantic_target_sha256(self.identity)

    @property
    def semantic_class_sha256(self) -> str:
        return semantic_class_sha256(
            lean_signature_sha256=self.lean_signature_sha256,
            tex_statement_sha256=self.tex_statement_sha256,
        )

    def descriptor(self) -> dict[str, str]:
        return {
            "semantic_target_sha256": self.semantic_target_sha256,
            "semantic_class_sha256": self.semantic_class_sha256,
            **self.identity,
            "lean_statement_sha256": self.lean_statement_sha256,
        }


@dataclass
class CurrentReceiptSurface:
    """Current cache/map/manifest facts used to reissue receipts."""

    paper: str
    cache_sha256: str
    source_map_sha256: str
    source_map_semantic_sha256: str
    source_route_inventory_sha256: str
    current_surface_sha256: str
    targets: list[CurrentReceiptTarget]
    source_route_inventory: dict[str, dict[str, Any]]
    direct_expression_semantics_review: bool = False
    source_record_audit_sha256: str = ""

    def input_pins(self) -> dict[str, str]:
        return {
            "cache_sha256": self.cache_sha256,
            "source_map_sha256": self.source_map_sha256,
            "source_route_inventory_sha256": self.source_route_inventory_sha256,
            "current_surface_sha256": self.current_surface_sha256,
            "direct_expression_semantics_review_policy_sha256": _digest(
                {
                    "version": (
                        review_dashboard.DIRECT_EXPRESSION_SEMANTICS_REVIEW_VERSION
                        if self.direct_expression_semantics_review
                        else "legacy_opt_out"
                    )
                }
            ),
            "source_record_audit_sha256": self.source_record_audit_sha256,
        }


@dataclass
class PriorSidecar:
    """Exact raw prior sidecar plus content-addressed item payload groups."""

    present: bool
    raw_bytes: bytes
    raw_sha256: str
    payload: dict[str, Any]
    groups: dict[str, list[dict[str, Any]]]

    def descriptor(self) -> dict[str, Any]:
        groups: list[dict[str, Any]] = []
        for digest, values in sorted(self.groups.items()):
            identity_by_digest: dict[str, dict[str, str]] = {}
            for value in values:
                identity = _entry_semantic_identity(value)
                if identity is not None:
                    identity_by_digest[_digest(identity)] = identity
            identities = sorted(
                identity_by_digest.values(), key=lambda value: _canonical_bytes(value)
            )
            cores = sorted(
                {
                    _entry_semantic_class(value)
                    for value in values
                    if _entry_semantic_class(value)
                }
            )
            groups.append(
                {
                    "payload_sha256": digest,
                    "occurrences": len(values),
                    "semantic_identities": identities,
                    "semantic_classes": cores,
                }
            )
        return {
            "present": self.present,
            "raw_sha256": self.raw_sha256 if self.present else None,
            "payload_groups": groups,
        }


@dataclass
class ReissueMaterialization:
    """Validated output plus an exact-byte archive payload."""

    sidecar: dict[str, Any]
    archive: dict[str, Any] | None
    report: dict[str, Any]


@dataclass(frozen=True)
class RecoveredManifestStoreInputs:
    """Raw, byte-pinned recovery bundle admitted before historic replay.

    The carrier on disk is intentionally retained only in its compressed form.
    ``HistoricalManifestReplayInputs.carrier_bytes`` is populated exclusively
    by the recovery verifier after it authenticates this bundle.
    """

    recovery_receipt: Mapping[str, Any]
    recovery_receipt_bytes: bytes
    recovery_receipt_path: str
    authority: Mapping[str, Any]
    authority_bytes: bytes
    authority_path: str
    carrier_compressed_bytes: bytes
    carrier_compressed_path: str


@dataclass(frozen=True)
class HistoricalManifestReplayInputs:
    """Exact historic artifacts admitted for one replay materialization.

    Paths are retrieval coordinates only.  The plan and the persisted receipt
    bind the raw artifact bytes.  Either the legacy carrier/authority pair or
    the verified recovered-store bundle authenticates the old semantic closure
    used by the bridge.
    """

    descriptor: Mapping[str, Any]
    receipt: Mapping[str, Any]
    receipt_bytes: bytes
    receipt_path: str
    carrier: Mapping[str, Any]
    carrier_bytes: bytes
    carrier_path: str | None
    authority: Mapping[str, Any]
    authority_bytes: bytes
    authority_path: str | None
    current_source_record_audit: Mapping[str, Any]
    current_source_record_audit_bytes: bytes
    current_source_record_audit_path: str
    current_lean_import_closure: Mapping[str, Any]
    current_lean_import_closure_bytes: bytes
    current_lean_import_closure_sha256: str
    prior_sidecar_archive_path: str
    recovered_manifest_store: RecoveredManifestStoreInputs | None = None


def _manifest_error(manifest: object, expected_signature: str) -> str:
    if not isinstance(manifest, Mapping):
        return "current cache row has no elaborated Lean signature manifest"
    recorded = _sha256(manifest.get("sha256"))
    if not recorded:
        return "current cache manifest has no valid SHA-256"
    try:
        calculated = review_dashboard.signature_manifest_digest(dict(manifest))
    except (TypeError, ValueError):
        return "current cache manifest cannot be canonically digested"
    if recorded != calculated:
        return "current cache manifest has an invalid canonical digest"
    if recorded != expected_signature:
        return "current cache row signature does not equal its manifest digest"
    return ""


def _route_inventory_digest(inventory: Mapping[str, Mapping[str, Any]]) -> str:
    """Digest source-route facts without relying on storage/navigation keys."""

    records: list[dict[str, Any]] = []
    for item in inventory.values():
        if not isinstance(item, Mapping):
            continue
        statement, digest = review_dashboard._source_item_coverage_statement(dict(item))
        locator = review_dashboard._source_item_coverage_location(dict(item))
        if not statement or not _sha256(digest) or not locator:
            continue
        records.append(
            {
                "statement_sha256": digest,
                "source_location": locator,
                "source_kind": str(item.get("source_kind") or "").strip().lower(),
                "source_status": str(item.get("source_status") or "").strip().lower(),
                "source_component_anchor_sha256": _sha256(
                    item.get("source_component_anchor_sha256")
                ),
            }
        )
    return _digest(sorted(records, key=lambda value: _canonical_bytes(value)))


def _surface_digest(targets: Iterable[CurrentReceiptTarget]) -> str:
    descriptors = [target.descriptor() for target in targets]
    return _digest(sorted(descriptors, key=lambda value: value["semantic_target_sha256"]))


def current_statement_receipt_surface(folder: Path) -> CurrentReceiptSurface:
    """Load a current, cache-backed review surface without re-elaborating Lean.

    A stale/missing cache is deliberately an error.  Reissue must not hide an
    expensive fresh Lean pass behind a mutation command; refresh the paper
    cache first, then use its current manifest facts exactly once.
    """

    folder = folder.resolve()
    cache_path = review_dashboard.paper_interface_cache_file(folder)
    map_path = folder / review_dashboard.PAPER_STATEMENT_MAP_FILE
    if not cache_path.is_file():
        raise StatementReceiptReissueError(
            "current paper-interface cache is unavailable; refresh the focused cache first"
        )
    if not map_path.is_file():
        raise StatementReceiptReissueError("current paper statement map is unavailable")
    cache_before = cache_path.read_bytes()
    map_before = map_path.read_bytes()
    rows = review_dashboard.load_cached_review_rows(folder, persist_rebind=False)
    cache_after = cache_path.read_bytes()
    map_after = map_path.read_bytes()
    if cache_before != cache_after or map_before != map_after:
        raise StatementReceiptReissueError(
            "cache or source map changed while loading the reissue surface; retry"
        )
    map_payload = _read_json_object(map_before, label="current paper statement map")
    map_semantic_sha256 = _sha256(source_map_cache_semantic_sha256(map_payload))
    if not map_semantic_sha256:
        raise StatementReceiptReissueError(
            "current paper statement map has no semantic cache digest"
        )
    if not rows:
        raise StatementReceiptReissueError(
            "paper-interface cache is stale or has no current review rows; refresh it first"
        )
    if not review_dashboard.llm_statement_source_routes_required(folder):
        raise StatementReceiptReissueError(
            "paper does not require explicit v10 source-route receipts"
        )

    inventory = review_dashboard.paper_statement_inventory(folder)
    # The map's statement digest is not enough by itself: it could still cite
    # an older transcript after a source artifact changed.  Reissue is a
    # current-evidence operation, so byte-validate the map's own pinned source
    # items before any reviewer body can be materialized.  This remains a
    # source-map check, not a name-based Lean routing heuristic.
    anchor_errors = review_dashboard._semantic_reuse_source_anchor_errors(
        folder, inventory.keys()
    )
    if anchor_errors:
        examples = "; ".join(
            f"{key}: {messages[0]}"
            for key, messages in sorted(anchor_errors.items())[:3]
            if messages
        )
        raise StatementReceiptReissueError(
            "current source-map anchors are not byte-valid for receipt reissue"
            + (f" ({examples})" if examples else "")
        )
    route_inventory: dict[str, dict[str, Any]] = dict(inventory)
    route_inventory.update(review_dashboard.paper_source_component_route_inventory(folder))
    route_inventory.update(
        review_dashboard.paper_source_definition_component_route_inventory(folder)
    )
    if not route_inventory:
        raise StatementReceiptReissueError("current source-route inventory is empty")

    raw_audit_path = folder / "audit" / "source_record_audit.json"
    if not raw_audit_path.is_file():
        raise StatementReceiptReissueError(
            "current source-record audit is unavailable for statement-receipt provenance"
        )
    raw_audit = _read_json_object(
        raw_audit_path.read_bytes(), label="current source-record audit"
    )
    if error := source_record_audit_receipt_error(raw_audit):
        raise StatementReceiptReissueError(
            "current source-record audit receipt is invalid: " + error
        )
    source_record_audit_sha256 = _required_sha256(
        raw_audit.get("source_record_audit_sha256"),
        label="current source-record audit digest",
    )

    targets_by_identity: dict[str, CurrentReceiptTarget] = {}
    # Assumption rows belong to the separate source-model provenance lane
    # (``assumption_match_llm.json``).  They intentionally need not name one
    # source-map item, so admitting them here would demand an impossible
    # direct statement route and duplicate the model review as a paper claim.
    for item in statement_receipt_review_rows(rows):
        signature = _required_sha256(
            item.lean_signature_sha256,
            label="current cache Lean signature",
        )
        paper_statement = review_dashboard.normalize_statement(item.paper_statement)
        translated_statement = review_dashboard.normalize_statement(item.agent_statement)
        if not paper_statement or not translated_statement:
            raise StatementReceiptReissueError(
                "current cache has a review row without a paper or translated statement"
            )
        paper_digest = review_dashboard.statement_digest(paper_statement)
        translated_digest = review_dashboard.statement_digest(translated_statement)
        if paper_digest == _EMPTY_STATEMENT_SHA256 or translated_digest == _EMPTY_STATEMENT_SHA256:
            raise StatementReceiptReissueError("current cache has an empty statement target")
        manifest = item.lean_signature_manifest
        if error := _manifest_error(manifest, signature):
            raise StatementReceiptReissueError(error)
        lean_digest = review_dashboard.statement_digest(item.lean_statement)
        if lean_digest == _EMPTY_STATEMENT_SHA256:
            raise StatementReceiptReissueError("current cache has an empty Lean statement")
        target = CurrentReceiptTarget(
            lean_signature_sha256=signature,
            paper_statement_sha256=paper_digest,
            tex_statement_sha256=translated_digest,
            lean_statement_sha256=lean_digest,
            manifest=copy.deepcopy(dict(manifest)),
        )
        identity_digest = target.semantic_target_sha256
        prior = targets_by_identity.get(identity_digest)
        if prior is not None and (
            prior.lean_statement_sha256 != target.lean_statement_sha256
            or _canonical_bytes(prior.manifest) != _canonical_bytes(target.manifest)
        ):
            raise StatementReceiptReissueError(
                "current cache has one semantic target with incompatible manifest or Lean text pins"
            )
        targets_by_identity[identity_digest] = target
        # Source-component targets are legitimate v10 targets but are not the
        # visible paper text.  Admit only a currently route-validated cache
        # target; the materializer still requires a fresh exact route ledger.
        component_digest = _sha256(item.llm_match_component_target_sha256)
        if component_digest and component_digest != paper_digest:
            component = CurrentReceiptTarget(
                lean_signature_sha256=signature,
                paper_statement_sha256=component_digest,
                tex_statement_sha256=translated_digest,
                lean_statement_sha256=lean_digest,
                manifest=copy.deepcopy(dict(manifest)),
            )
            component_key = component.semantic_target_sha256
            old_component = targets_by_identity.get(component_key)
            if old_component is not None and (
                old_component.lean_statement_sha256 != component.lean_statement_sha256
                or _canonical_bytes(old_component.manifest)
                != _canonical_bytes(component.manifest)
            ):
                raise StatementReceiptReissueError(
                    "current cache component target has incompatible manifest or Lean text pins"
                )
            targets_by_identity[component_key] = component

    targets = sorted(
        targets_by_identity.values(), key=lambda target: target.semantic_target_sha256
    )
    return CurrentReceiptSurface(
        paper=folder.name,
        cache_sha256=_bytes_sha256(cache_before),
        source_map_sha256=_bytes_sha256(map_before),
        source_map_semantic_sha256=map_semantic_sha256,
        source_route_inventory_sha256=_route_inventory_digest(route_inventory),
        current_surface_sha256=_surface_digest(targets),
        targets=targets,
        source_route_inventory=route_inventory,
        direct_expression_semantics_review=(
            review_dashboard.llm_direct_expression_semantics_review_required(folder)
        ),
        source_record_audit_sha256=source_record_audit_sha256,
    )


def _read_json_object(raw: bytes, *, label: str) -> dict[str, Any]:
    try:
        value = json.loads(raw.decode("utf-8"))
    except (UnicodeDecodeError, json.JSONDecodeError) as exc:
        raise StatementReceiptReissueError(f"{label} is not valid JSON") from exc
    if not isinstance(value, dict):
        raise StatementReceiptReissueError(f"{label} must be a JSON object")
    return value


def load_prior_sidecar(path: Path) -> PriorSidecar:
    """Load exact prior bytes and group entries by their canonical payload.

    The sidecar's item keys are intentionally not retained in the group
    identity.  Identical duplicate payloads form one group with an occurrence
    count; inconsistent duplicates remain separate content groups.
    """

    if not path.exists():
        return PriorSidecar(False, b"", "", {}, {})
    if not path.is_file():
        raise StatementReceiptReissueError("prior statement sidecar is not a regular file")
    return _prior_sidecar_from_raw(path.read_bytes(), label="prior statement sidecar")


def _prior_sidecar_from_raw(raw: bytes, *, label: str) -> PriorSidecar:
    """Parse a present sidecar while retaining its exact immutable bytes."""

    payload = _read_json_object(raw, label=label)
    items = payload.get("items")
    if not isinstance(items, Mapping):
        raise StatementReceiptReissueError(f"{label} has no object-valued items")
    groups: dict[str, list[dict[str, Any]]] = {}
    for value in items.values():
        # A non-object entry cannot be current evidence, but it can be retired
        # only by its exact content group.  Wrap it so its canonical digest is
        # still deterministic and never depends on its storage key.
        payload_value = copy.deepcopy(value) if isinstance(value, dict) else {"raw": value}
        groups.setdefault(_digest(payload_value), []).append(payload_value)
    return PriorSidecar(
        True,
        raw,
        _bytes_sha256(raw),
        payload,
        groups,
    )


def _entry_semantic_identity(entry: Mapping[str, Any]) -> dict[str, str] | None:
    identity = _target_identity(
        lean_signature_sha256=_sha256(entry.get("lean_signature_sha256")),
        paper_statement_sha256=_sha256(entry.get("paper_statement_sha256")),
        tex_statement_sha256=_sha256(entry.get("tex_statement_sha256")),
    )
    if not all(identity.values()) or identity["paper_statement_sha256"] == _EMPTY_STATEMENT_SHA256:
        return None
    return identity


def _entry_semantic_class(entry: Mapping[str, Any]) -> str:
    identity = _entry_semantic_identity(entry)
    if identity is None:
        return ""
    return semantic_class_sha256(
        lean_signature_sha256=identity["lean_signature_sha256"],
        tex_statement_sha256=identity["tex_statement_sha256"],
    )


def statement_receipt_reissue_template(
    surface: CurrentReceiptSurface, prior: PriorSidecar
) -> dict[str, Any]:
    """Create a non-evidence reviewer queue from current content identities."""

    return {
        "schema": REISSUE_SCHEMA,
        "artifact_kind": TEMPLATE_KIND,
        "policy_version": POLICY_VERSION,
        "paper": surface.paper,
        "current_inputs": surface.input_pins(),
        "current_targets": [target.descriptor() for target in surface.targets],
        "prior_sidecar": prior.descriptor(),
        "actions": [],
        "instructions": (
            "This is a non-evidence work queue. For every current target, supply "
            "one fresh reviewer-authored receipt or one exact current reuse. Every "
            "prior payload group must be fresh-superseded, reused, or explicitly "
            "retired. Do not use row keys, declaration names, or source-map keys as "
            "identity evidence."
        ),
        "non_evidence_scaffold": True,
        "must_not_be_written_to_repository_sidecar": True,
    }


def _prior_group_identity(values: Sequence[Mapping[str, Any]]) -> dict[str, str] | None:
    """Return a group identity only when every occurrence has one identity.

    Sidecar keys are deliberately absent here.  A payload group is useful for
    planning only when all of its repeated payloads make the same
    content-addressed claim; malformed groups remain conservatively
    unclassified for reuse.
    """

    identities: dict[str, dict[str, str]] = {}
    for value in values:
        identity = _entry_semantic_identity(value)
        if identity is None:
            return None
        identities[_digest(identity)] = identity
    if len(identities) != 1:
        return None
    return next(iter(identities.values()))


def _prior_group_semantic_class(values: Sequence[Mapping[str, Any]]) -> str:
    """Return a class only when the entire payload group has one valid class."""

    classes = {_entry_semantic_class(value) for value in values}
    classes.discard("")
    if len(classes) != 1:
        return ""
    # A group containing one malformed entry and one valid entry must not be
    # treated as a class match.  In normal sidecars canonical payload grouping
    # makes this impossible, but the check keeps the planner fail-closed.
    if any(not _entry_semantic_class(value) for value in values):
        return ""
    return next(iter(classes))


def _prior_group_descriptor(
    digest: str, values: Sequence[Mapping[str, Any]]
) -> dict[str, Any]:
    """Describe a prior group using only payload and semantic content pins."""

    identity = _prior_group_identity(values)
    semantic_class = _prior_group_semantic_class(values)
    out: dict[str, Any] = {
        "prior_entry_payload_sha256": digest,
        "occurrences": len(values),
        "semantic_class_sha256": semantic_class or None,
    }
    if identity is not None:
        out["semantic_identity"] = identity
    return out


def _exact_reuse_candidate_error(
    prior: PriorSidecar,
    values: Sequence[Mapping[str, Any]],
    *,
    target: CurrentReceiptTarget,
    surface: CurrentReceiptSurface,
) -> str:
    """Check whether one prior payload group is immediately reusable.

    This intentionally applies the same exact route and elaborated-manifest
    validation as materialization.  Equal target digests alone are not enough:
    a source-anchor, route, prompt, or semantic-ledger repair can invalidate a
    previously stored receipt while leaving its target triple unchanged.
    """

    if len(values) != 1:
        return "prior payload group has repeated occurrences and cannot be reused"
    entry = values[0]
    if _entry_semantic_identity(entry) != target.identity:
        return "prior payload identity is not the exact current target"
    return _prior_reuse_error(prior, entry, target=target, surface=surface)


def _candidate_action(
    action: str,
    *,
    target: CurrentReceiptTarget | None = None,
    prior_payload_sha256: str | None = None,
    supersedes: Sequence[str] = (),
    classification: str,
) -> dict[str, Any]:
    """Build a deliberately incomplete, non-materializable plan candidate."""

    out: dict[str, Any] = {
        "candidate_only": True,
        "action": action,
        "classification": classification,
    }
    if target is not None:
        out["target"] = target.descriptor()
    if prior_payload_sha256 is not None:
        out["prior_entry_payload_sha256"] = prior_payload_sha256
    if action == "fresh":
        out["supersedes_prior_entry_payload_sha256"] = sorted(set(supersedes))
        # A body is intentionally omitted.  This makes the candidate unusable
        # even if somebody manually changes its artifact kind.
        out["reviewer_body_required"] = True
    elif action == "retire":
        # A reason is intentionally omitted for the same reason: a semantic
        # anti-join must be stated by the reviewer, not inferred from this
        # classifier.
        out["reviewer_reason_required"] = True
    elif action == "reuse":
        out["requires_current_revalidation"] = True
    return out


def statement_receipt_reissue_action_scaffold(
    surface: CurrentReceiptSurface, prior: PriorSidecar
) -> dict[str, Any]:
    """Classify a current/prior surface without producing audit evidence.

    The planner uses only the three content-digest identity fields and their
    source-target-independent semantic class.  It never uses a sidecar key,
    declaration name, or source-map key to pair records.

    A same-class old receipt is tied to a fresh target only when that pairing
    is unique from content facts alone.  Multiple possible current targets are
    reported as unresolved rather than assigned based on navigation names.
    """

    targets_by_id = {
        target.semantic_target_sha256: target for target in surface.targets
    }
    targets_by_class: dict[str, list[CurrentReceiptTarget]] = {}
    for target in surface.targets:
        targets_by_class.setdefault(target.semantic_class_sha256, []).append(target)
    for values in targets_by_class.values():
        values.sort(key=lambda target: target.semantic_target_sha256)

    groups_by_class: dict[str, list[tuple[str, list[dict[str, Any]]]]] = {}
    unclassified_groups: list[tuple[str, list[dict[str, Any]]]] = []
    for digest, values in sorted(prior.groups.items()):
        semantic_class = _prior_group_semantic_class(values)
        if semantic_class:
            groups_by_class.setdefault(semantic_class, []).append((digest, values))
        else:
            unclassified_groups.append((digest, values))

    candidates: list[dict[str, Any]] = []
    unresolved: list[dict[str, Any]] = []
    covered_classes: set[str] = set()

    for semantic_class, class_targets in sorted(targets_by_class.items()):
        covered_classes.add(semantic_class)
        class_groups = groups_by_class.get(semantic_class, [])
        exact_valid: dict[str, list[tuple[str, list[dict[str, Any]]]]] = {}
        stale_groups: list[tuple[str, list[dict[str, Any]]]] = []

        for digest, values in class_groups:
            identity = _prior_group_identity(values)
            target_id = (
                semantic_target_sha256(identity) if identity is not None else ""
            )
            target = targets_by_id.get(target_id)
            if target is None or target.semantic_class_sha256 != semantic_class:
                stale_groups.append((digest, values))
                continue
            if _exact_reuse_candidate_error(
                prior, values, target=target, surface=surface
            ):
                stale_groups.append((digest, values))
                continue
            exact_valid.setdefault(target_id, []).append((digest, values))

        duplicate_exact_targets = {
            target_id
            for target_id, groups in exact_valid.items()
            if len(groups) != 1
        }
        if duplicate_exact_targets:
            unresolved.append(
                {
                    "candidate_only": True,
                    "classification": "multiple_exact_valid_prior_groups",
                    "semantic_class_sha256": semantic_class,
                    "current_targets": [
                        targets_by_id[target_id].descriptor()
                        for target_id in sorted(duplicate_exact_targets)
                    ],
                    "prior_payload_groups": [
                        _prior_group_descriptor(digest, values)
                        for target_id in sorted(duplicate_exact_targets)
                        for digest, values in exact_valid[target_id]
                    ],
                    "reviewer_resolution_required": True,
                }
            )
            # Do not make a hidden choice between competing independent
            # receipts.  The class is left entirely for a reviewer.
            continue

        valid_target_ids = set(exact_valid)
        unmatched_targets = [
            target
            for target in class_targets
            if target.semantic_target_sha256 not in valid_target_ids
        ]

        if stale_groups:
            if len(class_targets) == 1:
                # There is exactly one current source target in this class.
                # A fresh review can safely supersede every class-compatible
                # prior payload, including an otherwise-reusable old receipt.
                target = class_targets[0]
                candidates.append(
                    _candidate_action(
                        "fresh",
                        target=target,
                        supersedes=[digest for digest, _ in class_groups],
                        classification="same_semantic_class_stale_source_identity",
                    )
                )
                continue
            if len(unmatched_targets) == 1:
                # Existing exact receipts remain reusable.  The sole new or
                # changed target is the only content-addressable destination
                # for the stale class-compatible history.
                for target_id, groups in sorted(exact_valid.items()):
                    candidates.append(
                        _candidate_action(
                            "reuse",
                            target=targets_by_id[target_id],
                            prior_payload_sha256=groups[0][0],
                            classification="exact_valid_identity_match",
                        )
                    )
                candidates.append(
                    _candidate_action(
                        "fresh",
                        target=unmatched_targets[0],
                        supersedes=[digest for digest, _ in stale_groups],
                        classification="same_semantic_class_stale_source_identity",
                    )
                )
                continue

            unresolved.append(
                {
                    "candidate_only": True,
                    "classification": "ambiguous_same_semantic_class_supersession",
                    "semantic_class_sha256": semantic_class,
                    "current_targets": [
                        target.descriptor() for target in class_targets
                    ],
                    "prior_payload_groups": [
                        _prior_group_descriptor(digest, values)
                        for digest, values in class_groups
                    ],
                    "reviewer_resolution_required": True,
                }
            )
            continue

        # No stale prior history exists in the class.  Exact-valid receipts
        # are reuse candidates; genuinely new targets need a full fresh body.
        for target in class_targets:
            groups = exact_valid.get(target.semantic_target_sha256, [])
            if groups:
                candidates.append(
                    _candidate_action(
                        "reuse",
                        target=target,
                        prior_payload_sha256=groups[0][0],
                        classification="exact_valid_identity_match",
                    )
                )
            else:
                candidates.append(
                    _candidate_action(
                        "fresh",
                        target=target,
                        classification="no_prior_semantic_class_match",
                    )
                )

    # A prior group that has no current Lean/translation semantic class is an
    # orphan candidate.  The actual plan still requires a reviewer-authored
    # anti-join reason, so this does not silently delete anything.
    for semantic_class, class_groups in sorted(groups_by_class.items()):
        if semantic_class in covered_classes:
            continue
        for digest, _values in class_groups:
            candidates.append(
                _candidate_action(
                    "retire",
                    prior_payload_sha256=digest,
                    classification="no_current_semantic_class_match",
                )
            )
    for digest, _values in unclassified_groups:
        candidates.append(
            _candidate_action(
                "retire",
                prior_payload_sha256=digest,
                classification="prior_payload_has_no_valid_semantic_identity",
            )
        )

    action_order = {"fresh": 0, "reuse": 1, "retire": 2}
    candidates.sort(
        key=lambda action: (
            action_order[str(action["action"])],
            str(action.get("target", {}).get("semantic_target_sha256") or ""),
            str(action.get("prior_entry_payload_sha256") or ""),
        )
    )
    return {
        "schema": REISSUE_SCHEMA,
        "artifact_kind": ACTION_SCAFFOLD_KIND,
        "policy_version": POLICY_VERSION,
        "paper": surface.paper,
        "current_inputs": surface.input_pins(),
        "current_targets": [target.descriptor() for target in surface.targets],
        "prior_sidecar": prior.descriptor(),
        "candidate_actions": candidates,
        "unresolved_semantic_classes": unresolved,
        "instructions": (
            "This is a non-evidence action scaffold, not a reissue plan. It is "
            "content-addressed only: do not use row keys, declaration names, or "
            "source-map keys to resolve an unresolved class. Build a new plan with "
            "a complete reviewer-authored body for every fresh action and a "
            "substantive anti-join reason for every retire action. Revalidate the "
            "surface immediately before materialization."
        ),
        "non_evidence_scaffold": True,
        "must_not_be_written_to_repository_sidecar": True,
    }


def _candidate_marker_error(value: object, *, label: str, path: str = "") -> str:
    if isinstance(value, Mapping):
        for raw_key, child in value.items():
            key = str(raw_key).strip()
            here = f"{path}.{key}" if path else key
            if key in _CANDIDATE_MARKERS and bool(child):
                return f"{label} carries non-evidence marker `{here}`"
            if error := _candidate_marker_error(child, label=label, path=here):
                return error
    elif isinstance(value, list):
        for index, child in enumerate(value):
            if error := _candidate_marker_error(child, label=label, path=f"{path}[{index}]"):
                return error
    return ""


def _target_from_descriptor(
    raw: object,
    targets: Mapping[str, CurrentReceiptTarget],
) -> CurrentReceiptTarget:
    if not isinstance(raw, Mapping):
        raise StatementReceiptReissueError("action target must be an object")
    target_id = _required_sha256(
        raw.get("semantic_target_sha256"), label="action target semantic_target_sha256"
    )
    target = targets.get(target_id)
    if target is None:
        raise StatementReceiptReissueError(
            "action target is not a current content-addressed cache target"
        )
    expected = target.descriptor()
    for field, value in expected.items():
        if str(raw.get(field) or "").strip().lower() != value.lower():
            raise StatementReceiptReissueError(
                f"action target has stale or incomplete `{field}` pin"
            )
    return target


def _current_surface_error(plan: Mapping[str, Any], surface: CurrentReceiptSurface) -> str:
    if plan.get("schema") != REISSUE_SCHEMA:
        return "plan has an unsupported schema"
    if plan.get("artifact_kind") != PLAN_KIND:
        return "plan has the wrong artifact_kind"
    if plan.get("policy_version") != POLICY_VERSION:
        return "plan has the wrong policy_version"
    if plan.get("paper") != surface.paper:
        return "plan names a different paper"
    if error := _candidate_marker_error(plan, label="plan"):
        return error
    pins = plan.get("current_inputs")
    if not isinstance(pins, Mapping):
        return "plan has no current input pins"
    for field, expected in surface.input_pins().items():
        if _sha256(pins.get(field)) != expected:
            return f"plan has a stale `{field}` pin"
    return ""


def _prior_plan_error(plan: Mapping[str, Any], prior: PriorSidecar) -> str:
    descriptor = plan.get("prior_sidecar")
    if not isinstance(descriptor, Mapping):
        return "plan has no prior-sidecar descriptor"
    if descriptor.get("present") is not prior.present:
        return "plan has a stale prior-sidecar presence pin"
    if prior.present:
        if _sha256(descriptor.get("raw_sha256")) != prior.raw_sha256:
            return "plan has a stale prior-sidecar raw-byte digest"
    elif descriptor.get("raw_sha256") not in {None, ""}:
        return "plan claims raw bytes for an absent prior sidecar"
    expected_groups = prior.descriptor().get("payload_groups")
    if descriptor.get("payload_groups") != expected_groups:
        return "plan has a stale prior-sidecar payload-group ledger"
    return ""


def _target_storage_key(target: CurrentReceiptTarget) -> str:
    """Use a content address as storage navigation, never a declaration name."""

    return "semantic_" + target.semantic_target_sha256


def _body_error(body: object) -> str:
    if not isinstance(body, Mapping):
        return "fresh action has no object-valued reviewer body"
    if error := _candidate_marker_error(body, label="fresh reviewer body"):
        return error
    # A reviewer will often start from a prior receipt, whose ordinary ledger
    # necessarily contains current-signature fields.  Those fields are not
    # trusted or copied: the materializer removes them and derives all of them
    # again below.  ``semantic_reuse_v1`` is different: it purports to carry
    # historical evidence and therefore cannot appear in a fresh body at all.
    if "semantic_reuse_v1" in body:
        return "fresh reviewer body cannot carry semantic_reuse_v1 evidence"
    return ""


def _reviewer_body_without_transport(body: Mapping[str, Any]) -> dict[str, Any]:
    """Drop target/validator transport fields before binding a fresh body.

    This lets a reviewer use an old receipt as a writing scaffold without
    allowing its stale target pins, prompt, or reviewer identity to survive.
    The semantic ledger itself is retained and then validated against the
    current elaborated manifest and source route inventory.
    """

    out = copy.deepcopy(dict(body))
    for field in _FRESH_GENERATED_FIELDS:
        out.pop(field, None)
    return out


def _effective_source_definition_review_required(
    entry: Mapping[str, Any],
    inventory: Mapping[str, Mapping[str, Any]],
    *,
    include_direct_expressions: bool,
) -> bool:
    return bool(
        review_dashboard.direct_source_definition_route_keys(
            dict(entry),
            inventory=dict(inventory),
            include_direct_expressions=include_direct_expressions,
        )
    )


def _current_entry_error(
    entry: Mapping[str, Any],
    *,
    target: CurrentReceiptTarget,
    surface: CurrentReceiptSurface,
    sidecar_prompt_version: str = "",
) -> str:
    identity = _entry_semantic_identity(entry)
    if identity != target.identity:
        return "entry target identity does not equal its exact current cache target"
    if _sha256(entry.get("lean_statement_sha256")) != target.lean_statement_sha256:
        return "entry has a stale Lean statement digest"
    prompt_version = str(
        entry.get("prompt_version") or sidecar_prompt_version or ""
    ).strip()
    if prompt_version != review_dashboard.REQUIRED_LLM_STATEMENT_PROMPT_VERSION:
        return "entry has a stale statement-review prompt version"
    ledger_error = review_dashboard.semantic_obligation_ledger_error(
        dict(entry),
        dict(target.manifest),
        require_source_definition_semantics_review=(
            _effective_source_definition_review_required(
                entry,
                surface.source_route_inventory,
                include_direct_expressions=(
                    surface.direct_expression_semantics_review
                ),
            )
        ),
    )
    if ledger_error:
        return "semantic obligation ledger is invalid: " + ledger_error
    route_error = review_dashboard.source_route_pin_error(
        dict(entry),
        inventory=surface.source_route_inventory,
        require_statement_target=True,
        require_verbatim_source_inputs=(
            review_dashboard.statement_review_requires_verbatim_source_inputs(
                entry
            )
        ),
    )
    if route_error:
        return "source-route receipt is invalid: " + route_error
    return ""


def historical_manifest_replay_current_targets(
    surface: CurrentReceiptSurface,
) -> list[dict[str, object]]:
    """Return name-free current facts for a frozen historic-manifest bridge.

    A replay bridge needs a per-target manifest and a source-route receipt in
    addition to the three target identity hashes.  The route receipt combines
    the exact current target identity with the complete current route
    inventory: the later entry validator still checks each transported entry's
    concrete routes against that inventory.  This deliberately over-binds a
    bridge to all current route facts rather than trying to recover a target
    association from a storage key or Lean declaration spelling.
    """

    return [
        {
            **target.identity,
            "lean_signature_manifest": copy.deepcopy(dict(target.manifest)),
            "source_route_sha256": historical_manifest_replay_target_source_route_sha256(
                target, surface
            ),
        }
        for target in surface.targets
    ]


def historical_manifest_replay_runner_targets(
    folder: Path,
    surface: CurrentReceiptSurface,
    *,
    navigation_field: str = "declaration",
) -> list[dict[str, object]]:
    """Attach transient Lean routes to exact current content targets.

    The bridge's persisted target interface is deliberately name-free.  The
    historic Lean serializer nevertheless needs a fully qualified declaration
    to elaborate.  This generation-only adapter rebuilds the cache-to-target
    association from the exact current content triple, rejects an ambiguous
    route, and appends the declaration only to the in-memory runner request.
    The runner strips this field before it returns any observation, and no
    subsequent bridge matching consults it.
    """

    folder = folder.resolve()
    cache_path = review_dashboard.paper_interface_cache_file(folder)
    try:
        cache_before = cache_path.read_bytes()
        rows = review_dashboard.load_cached_review_rows(
            folder, persist_rebind=False
        )
        cache_after = cache_path.read_bytes()
    except (OSError, ValueError) as exc:
        raise StatementReceiptReissueError(
            "could not read the current paper-interface cache for historic routing"
        ) from exc
    if cache_before != cache_after or _bytes_sha256(cache_before) != surface.cache_sha256:
        raise StatementReceiptReissueError(
            "paper-interface cache changed or does not equal the frozen current receipt surface"
        )
    if not rows:
        raise StatementReceiptReissueError(
            "paper-interface cache has no current rows for historic routing"
        )

    declarations_by_target: dict[str, set[str]] = {}
    expected_targets = {
        target.semantic_target_sha256: target for target in surface.targets
    }

    def add_route(
        *,
        lean_signature_sha256: str,
        paper_statement_sha256: str,
        tex_statement_sha256: str,
        declaration: str,
    ) -> None:
        identity = _target_identity(
            lean_signature_sha256=lean_signature_sha256,
            paper_statement_sha256=paper_statement_sha256,
            tex_statement_sha256=tex_statement_sha256,
        )
        target_id = semantic_target_sha256(identity)
        if target_id not in expected_targets:
            return
        declarations_by_target.setdefault(target_id, set()).add(declaration)

    for item in rows:
        declaration = str(getattr(item, "full_name", "") or "").strip()
        if not declaration:
            raise StatementReceiptReissueError(
                "current paper-interface cache row has no fully qualified transient route"
            )
        try:
            signature = _required_sha256(
                getattr(item, "lean_signature_sha256", ""),
                label="current cache Lean signature",
            )
            paper_digest = review_dashboard.statement_digest(
                review_dashboard.normalize_statement(
                    getattr(item, "paper_statement", "")
                )
            )
            translation_digest = review_dashboard.statement_digest(
                review_dashboard.normalize_statement(
                    getattr(item, "agent_statement", "")
                )
            )
        except (TypeError, ValueError) as exc:
            raise StatementReceiptReissueError(
                "current paper-interface cache row cannot be content-addressed for historic routing"
            ) from exc
        if paper_digest == _EMPTY_STATEMENT_SHA256 or translation_digest == _EMPTY_STATEMENT_SHA256:
            raise StatementReceiptReissueError(
                "current paper-interface cache row has an empty historic-routing target"
            )
        add_route(
            lean_signature_sha256=signature,
            paper_statement_sha256=paper_digest,
            tex_statement_sha256=translation_digest,
            declaration=declaration,
        )
        component_digest = _sha256(
            getattr(item, "llm_match_component_target_sha256", "")
        )
        if component_digest and component_digest != paper_digest:
            add_route(
                lean_signature_sha256=signature,
                paper_statement_sha256=component_digest,
                tex_statement_sha256=translation_digest,
                declaration=declaration,
            )

    routed_targets: list[dict[str, object]] = []
    for target in historical_manifest_replay_current_targets(surface):
        identity = _target_identity(
            lean_signature_sha256=_sha256(target.get("lean_signature_sha256")),
            paper_statement_sha256=_sha256(target.get("paper_statement_sha256")),
            tex_statement_sha256=_sha256(target.get("tex_statement_sha256")),
        )
        target_id = semantic_target_sha256(identity)
        declarations = declarations_by_target.get(target_id, set())
        if len(declarations) != 1:
            detail = "none" if not declarations else "multiple"
            raise StatementReceiptReissueError(
                "historic serializer routing is not uniquely determined by the "
                f"current content target ({detail} declarations)"
            )
        routed = copy.deepcopy(target)
        routed[navigation_field] = next(iter(declarations))
        routed_targets.append(routed)
    return routed_targets


def historical_manifest_replay_target_source_route_sha256(
    target: CurrentReceiptTarget,
    surface: CurrentReceiptSurface,
) -> str:
    """Return the name-free target/route receipt used in a replay bridge."""

    return _digest(
        {
            "schema": 1,
            "target_identity": target.identity,
            "source_route_inventory_sha256": surface.source_route_inventory_sha256,
        }
    )


def historical_manifest_replay_current_evidence_sha256(
    surface: CurrentReceiptSurface,
) -> str:
    """Content-pin the full current surface used by a replay bridge.

    The manifest serializer bridge is not an alternative source-route audit.
    This receipt binds it to the same cache, source-map, route inventory, and
    direct-expression policy facts that ordinary receipt materialization uses.
    """

    return _digest(
        {
            "schema": 1,
            "current_inputs": surface.input_pins(),
            "current_surface_sha256": surface.current_surface_sha256,
        }
    )


def _historical_manifest_replay_target_validator(
    surface: CurrentReceiptSurface,
    raw: Mapping[str, object],
) -> str:
    """Check an injected bridge target against this exact current surface."""

    identity = _target_identity(
        lean_signature_sha256=_sha256(raw.get("lean_signature_sha256")),
        paper_statement_sha256=_sha256(raw.get("paper_statement_sha256")),
        tex_statement_sha256=_sha256(raw.get("tex_statement_sha256")),
    )
    if not all(identity.values()):
        return "current replay target has an incomplete content identity"
    target_id = semantic_target_sha256(identity)
    targets = {target.semantic_target_sha256: target for target in surface.targets}
    target = targets.get(target_id)
    if target is None:
        return "current replay target is not an exact current content target"
    manifest = raw.get("lean_signature_manifest")
    if not isinstance(manifest, Mapping) or _canonical_bytes(dict(manifest)) != _canonical_bytes(
        dict(target.manifest)
    ):
        return "current replay target manifest differs from the current cache"
    if _sha256(raw.get("source_route_sha256")) != historical_manifest_replay_target_source_route_sha256(
        target, surface
    ):
        return "current replay target source-route receipt is stale"
    return ""


def _historical_manifest_replay_source_route_validator(
    surface: CurrentReceiptSurface,
    raw: Mapping[str, object],
) -> str:
    """Require the bridge's route receipt to be the current global inventory."""

    identity = _target_identity(
        lean_signature_sha256=_sha256(raw.get("lean_signature_sha256")),
        paper_statement_sha256=_sha256(raw.get("paper_statement_sha256")),
        tex_statement_sha256=_sha256(raw.get("tex_statement_sha256")),
    )
    if not all(identity.values()):
        return "current replay source-route target identity is incomplete"
    target = next(
        (
            candidate
            for candidate in surface.targets
            if candidate.identity == identity
        ),
        None,
    )
    if target is None or _sha256(
        raw.get("source_route_sha256")
    ) != historical_manifest_replay_target_source_route_sha256(target, surface):
        return "current replay source-route inventory is stale"
    return ""


def _normalized_paper_relative_path_text(value: object, *, label: str) -> str:
    """Validate a path coordinate without treating it as evidence identity."""

    text = str(value or "").strip()
    pure = PurePosixPath(text)
    if (
        not text
        or pure.is_absolute()
        or any(part in {"", ".", ".."} for part in pure.parts)
        or pure.as_posix() != text
    ):
        raise StatementReceiptReissueError(
            f"{label} must be a canonical paper-relative path"
        )
    return text


def _plan_pinned_historical_json_artifact(
    *,
    label: str,
    planned_path: object,
    planned_bytes_sha256: object,
    supplied_path: str | None,
    supplied_bytes: bytes | None,
    supplied_object: object,
) -> tuple[str, dict[str, Any], bytes]:
    """Validate one exact-byte historic input named only for retrieval."""

    path = _normalized_paper_relative_path_text(planned_path, label=f"{label} path")
    if supplied_path != path:
        raise StatementReceiptReissueError(f"{label} path does not equal the plan pin")
    if supplied_bytes is None:
        raise StatementReceiptReissueError(f"{label} requires its plan-pinned bytes")
    expected_sha = _required_sha256(
        planned_bytes_sha256, label=f"{label} bytes_sha256"
    )
    if _bytes_sha256(supplied_bytes) != expected_sha:
        raise StatementReceiptReissueError(f"{label} bytes differ from the plan pin")
    parsed = _read_json_object(supplied_bytes, label=label)
    if not isinstance(supplied_object, Mapping) or dict(supplied_object) != parsed:
        raise StatementReceiptReissueError(
            f"{label} object differs from its exact bytes"
        )
    return path, parsed, supplied_bytes


def _plan_pinned_historical_bytes_artifact(
    *,
    label: str,
    planned_path: object,
    planned_bytes_sha256: object,
    supplied_path: str | None,
    supplied_bytes: bytes | None,
) -> tuple[str, bytes]:
    """Validate one opaque, exact-byte historic input named for retrieval.

    A recovered carrier is compressed on disk.  Do not decode it here: the
    recovery receipt verifier is the only component permitted to turn those
    stored bytes into a manifest carrier.
    """

    path = _normalized_paper_relative_path_text(planned_path, label=f"{label} path")
    if supplied_path != path:
        raise StatementReceiptReissueError(f"{label} path does not equal the plan pin")
    if supplied_bytes is None:
        raise StatementReceiptReissueError(f"{label} requires its plan-pinned bytes")
    expected_sha = _required_sha256(
        planned_bytes_sha256, label=f"{label} bytes_sha256"
    )
    if _bytes_sha256(supplied_bytes) != expected_sha:
        raise StatementReceiptReissueError(f"{label} bytes differ from the plan pin")
    return path, supplied_bytes


def _recovered_manifest_store_metadata(
    value: object,
    *,
    label: str,
) -> dict[str, str]:
    """Normalize the raw stored-artifact pins for a recovered store bundle."""

    if not isinstance(value, Mapping) or set(value) != HISTORICAL_REPLAY_RECOVERED_STORE_FIELDS:
        raise StatementReceiptReissueError(
            f"{label} has unsupported or missing fields"
        )
    return {
        "recovery_receipt_path": _normalized_paper_relative_path_text(
            value.get("recovery_receipt_path"),
            label=f"{label} recovery_receipt_path",
        ),
        "recovery_receipt_bytes_sha256": _required_sha256(
            value.get("recovery_receipt_bytes_sha256"),
            label=f"{label} recovery_receipt_bytes_sha256",
        ),
        "authority_path": _normalized_paper_relative_path_text(
            value.get("authority_path"), label=f"{label} authority_path"
        ),
        "authority_bytes_sha256": _required_sha256(
            value.get("authority_bytes_sha256"),
            label=f"{label} authority_bytes_sha256",
        ),
        "carrier_compressed_path": _normalized_paper_relative_path_text(
            value.get("carrier_compressed_path"),
            label=f"{label} carrier_compressed_path",
        ),
        "carrier_compressed_bytes_sha256": _required_sha256(
            value.get("carrier_compressed_bytes_sha256"),
            label=f"{label} carrier_compressed_bytes_sha256",
        ),
    }


def _verified_recovered_manifest_store_bundle(
    *,
    paper: str,
    descriptor: object,
    recovery_receipt: object,
    recovery_receipt_bytes: bytes | None,
    recovery_receipt_path: str | None,
    authority: object,
    authority_bytes: bytes | None,
    authority_path: str | None,
    carrier_compressed_bytes: bytes | None,
    carrier_compressed_path: str | None,
    label: str,
) -> tuple[
    RecoveredManifestStoreInputs,
    dict[str, Any],
    dict[str, Any],
    bytes,
]:
    """Authenticate raw recovery artifacts before exposing a carrier mapping.

    The returned carrier object and raw bytes are *only* the output of
    ``verified_recovered_manifest_store_artifacts``.  This keeps the historic
    replay validator unaware of the compressed storage representation while
    preventing an unverified decompression path from becoming evidence.
    """

    metadata = _recovered_manifest_store_metadata(descriptor, label=label)
    receipt_path, parsed_receipt, exact_receipt_bytes = (
        _plan_pinned_historical_json_artifact(
            label=f"{label} recovery receipt",
            planned_path=metadata["recovery_receipt_path"],
            planned_bytes_sha256=metadata["recovery_receipt_bytes_sha256"],
            supplied_path=recovery_receipt_path,
            supplied_bytes=recovery_receipt_bytes,
            supplied_object=recovery_receipt,
        )
    )
    authority_path_text, parsed_authority, exact_authority_bytes = (
        _plan_pinned_historical_json_artifact(
            label=f"{label} authority",
            planned_path=metadata["authority_path"],
            planned_bytes_sha256=metadata["authority_bytes_sha256"],
            supplied_path=authority_path,
            supplied_bytes=authority_bytes,
            supplied_object=authority,
        )
    )
    carrier_path, exact_carrier_compressed_bytes = _plan_pinned_historical_bytes_artifact(
        label=f"{label} compressed carrier",
        planned_path=metadata["carrier_compressed_path"],
        planned_bytes_sha256=metadata["carrier_compressed_bytes_sha256"],
        supplied_path=carrier_compressed_path,
        supplied_bytes=carrier_compressed_bytes,
    )
    try:
        verified_authority, verified_carrier, raw_carrier = (
            historical_manifest_store_recovery.verified_recovered_manifest_store_artifacts(
                paper=paper,
                receipt=parsed_receipt,
                receipt_bytes=exact_receipt_bytes,
                authority_bytes=exact_authority_bytes,
                carrier_compressed_bytes=exact_carrier_compressed_bytes,
            )
        )
    except historical_manifest_store_recovery.HistoricalManifestStoreRecoveryError as exc:
        raise StatementReceiptReissueError(
            f"{label} recovery bundle does not verify: {exc}"
        ) from exc
    if verified_authority != parsed_authority:
        raise StatementReceiptReissueError(
            f"{label} recovery verifier returned authority different from its raw bytes"
        )
    recovered_store = parsed_receipt.get("recovered_store")
    if not isinstance(recovered_store, Mapping):  # Verified above; keep path binding local.
        raise StatementReceiptReissueError(f"{label} recovery receipt has no recovered store")
    receipt_coordinate = _normalized_paper_relative_path_text(
        recovered_store.get("receipt_paper_relative_path"),
        label=f"{label} recovery receipt stored path",
    )
    authority_metadata = recovered_store.get("authority")
    carrier_metadata = recovered_store.get("carrier")
    if not isinstance(authority_metadata, Mapping) or not isinstance(carrier_metadata, Mapping):
        raise StatementReceiptReissueError(
            f"{label} recovery receipt has malformed stored-artifact coordinates"
        )
    authority_coordinate = _normalized_paper_relative_path_text(
        authority_metadata.get("paper_relative_path"),
        label=f"{label} recovery authority stored path",
    )
    carrier_coordinate = _normalized_paper_relative_path_text(
        carrier_metadata.get("paper_relative_path"),
        label=f"{label} recovery compressed carrier stored path",
    )
    if (
        receipt_coordinate != receipt_path
        or authority_coordinate != authority_path_text
        or carrier_coordinate != carrier_path
    ):
        raise StatementReceiptReissueError(
            f"{label} recovery receipt stored-artifact coordinates differ from plan pins"
        )
    return (
        RecoveredManifestStoreInputs(
            recovery_receipt=parsed_receipt,
            recovery_receipt_bytes=exact_receipt_bytes,
            recovery_receipt_path=receipt_path,
            authority=verified_authority,
            authority_bytes=exact_authority_bytes,
            authority_path=authority_path_text,
            carrier_compressed_bytes=exact_carrier_compressed_bytes,
            carrier_compressed_path=carrier_path,
        ),
        verified_authority,
        verified_carrier,
        raw_carrier,
    )


def _canonical_lean_import_closure_bytes(closure: Mapping[str, object]) -> bytes:
    """Return the one canonical byte form accepted by the historic runner."""

    try:
        return historical_manifest_runner.current_lean_import_closure_canonical_bytes(
            closure
        )
    except historical_manifest_runner.HistoricalStatementManifestRunnerError as exc:
        raise StatementReceiptReissueError(
            "current Lean import-closure cannot be canonically encoded"
        ) from exc


def _validated_current_source_record_closure_authority(
    surface: CurrentReceiptSurface,
    raw_audit: Mapping[str, object],
) -> tuple[dict[str, Any], bytes, str]:
    """Extract a current Lean closure only from an authenticated raw audit.

    The source-record raw receipt is not treated as a generic JSON container.
    Its own aggregate/raw receipts, source-map semantic pin, full Lean-source
    inventory, and the current cache manifests must all agree with the
    Lean-authored import closure.  Declaration spellings are not used for a
    target match; module/path data is used solely to establish that the cache
    and executable closure describe the same loaded environment.
    """

    if str(raw_audit.get("paper") or "").strip() != surface.paper:
        raise StatementReceiptReissueError(
            "current source-record closure authority belongs to a different paper"
        )
    if error := source_record_audit_receipt_error(raw_audit):
        raise StatementReceiptReissueError(
            "current source-record closure authority has invalid raw receipts: "
            + error
        )
    if error := source_record_target_route_error(raw_audit):
        raise StatementReceiptReissueError(
            "current source-record closure authority has invalid target routing: "
            + error
        )
    fingerprint = raw_audit.get("source_record_input_fingerprint")
    if not isinstance(fingerprint, Mapping):
        raise StatementReceiptReissueError(
            "current source-record closure authority has no input fingerprint"
        )
    if (
        str(fingerprint.get("paper") or "").strip() != surface.paper
        or fingerprint.get("no_lean") is not False
    ):
        raise StatementReceiptReissueError(
            "current source-record closure authority is not a completed current-paper receipt"
        )
    if _sha256(fingerprint.get("paper_statement_map_semantic_sha256")) != (
        surface.source_map_semantic_sha256
    ):
        raise StatementReceiptReissueError(
            "current source-record closure authority has a stale source-map semantic pin"
        )
    raw_closure = raw_audit.get("lean_import_closure")
    try:
        closure = lean_import_closure.validated_lean_import_closure_payload(
            raw_closure
        )
    except (TypeError, ValueError) as exc:
        raise StatementReceiptReissueError(
            "current source-record closure authority has an invalid Lean import closure"
        ) from exc
    try:
        closure_sha = historical_manifest_runner.current_lean_import_closure_payload_sha256(
            closure
        )
    except historical_manifest_runner.HistoricalStatementManifestRunnerError as exc:
        raise StatementReceiptReissueError(
            "current source-record closure authority cannot be canonically digested"
        ) from exc
    if _sha256(fingerprint.get("lean_import_closure_sha256")) != closure_sha:
        raise StatementReceiptReissueError(
            "current source-record closure authority has a stale Lean import-closure pin"
        )

    expected_entrypoint = f"papers/{surface.paper}/PaperInterface.lean"
    expected_module = lean_import_closure.module_name_for_path(expected_entrypoint)
    if (
        closure.get("entrypoint") != expected_entrypoint
        or closure.get("entry_module") != expected_module
    ):
        raise StatementReceiptReissueError(
            "current source-record closure authority is not bound to this PaperInterface"
        )
    closure_sources = closure.get("sources")
    if not isinstance(closure_sources, list):  # Checked above; keeps types local.
        raise StatementReceiptReissueError(
            "current source-record closure authority has no source inventory"
        )
    closure_source_by_path: dict[str, str] = {}
    closure_modules: set[str] = set()
    for raw_source in closure_sources:
        if not isinstance(raw_source, Mapping):
            raise StatementReceiptReissueError(
                "current source-record closure authority has a malformed source inventory"
            )
        path = str(raw_source.get("path") or "").strip()
        digest = _sha256(raw_source.get("sha256"))
        module = str(raw_source.get("module") or "").strip()
        if not path or not digest or not module or path in closure_source_by_path:
            raise StatementReceiptReissueError(
                "current source-record closure authority has a malformed source identity"
            )
        closure_source_by_path[path] = digest
        closure_modules.add(module)
    raw_dependencies = fingerprint.get("lean_dependency_identities")
    if not isinstance(raw_dependencies, list):
        raise StatementReceiptReissueError(
            "current source-record closure authority has no Lean dependency inventory"
        )
    fingerprint_sources: dict[str, str] = {}
    for raw_dependency in raw_dependencies:
        if not isinstance(raw_dependency, Mapping):
            raise StatementReceiptReissueError(
                "current source-record closure authority has a malformed Lean dependency inventory"
            )
        if raw_dependency.get("status") != "present":
            raise StatementReceiptReissueError(
                "current source-record closure authority has a non-present Lean dependency"
            )
        path = str(raw_dependency.get("path") or "").strip()
        digest = _sha256(raw_dependency.get("sha256"))
        if not path or not digest or path in fingerprint_sources:
            raise StatementReceiptReissueError(
                "current source-record closure authority has a malformed Lean dependency identity"
            )
        fingerprint_sources[path] = digest
    if fingerprint_sources != closure_source_by_path:
        raise StatementReceiptReissueError(
            "current source-record closure authority source inventory does not equal its fingerprint"
        )
    interface_source = fingerprint.get("review_interface_source")
    if not isinstance(interface_source, Mapping) or (
        str(interface_source.get("path") or "").strip() != expected_entrypoint
        or _sha256(interface_source.get("sha256"))
        != closure_source_by_path.get(expected_entrypoint)
    ):
        raise StatementReceiptReissueError(
            "current source-record closure authority has no matching PaperInterface source pin"
        )

    closure_controls = closure.get("build_controls")
    if not isinstance(closure_controls, list):
        raise StatementReceiptReissueError(
            "current source-record closure authority has no build-control inventory"
        )
    control_by_path = {
        str(control.get("path") or "").strip(): _sha256(control.get("sha256"))
        for control in closure_controls
        if isinstance(control, Mapping)
    }
    if any(not path or not digest for path, digest in control_by_path.items()):
        raise StatementReceiptReissueError(
            "current source-record closure authority has malformed build controls"
        )
    for target in surface.targets:
        manifest = target.manifest
        graph = manifest.get("semantic_dependency_graph")
        nodes = graph.get("nodes") if isinstance(graph, Mapping) else None
        if not isinstance(nodes, list):
            raise StatementReceiptReissueError(
                "current cache target has no semantic dependency graph for closure validation"
            )
        target_modules = {
            str(node.get("module_origin") or "").strip()
            for node in nodes
            if isinstance(node, Mapping) and str(node.get("module_origin") or "").strip()
        }
        if not target_modules or not target_modules.issubset(
            set(closure.get("lean_loaded_modules") or [])
        ):
            raise StatementReceiptReissueError(
                "current cache manifest is not contained in the source-record Lean closure"
            )
        environment = manifest.get("semantic_dependency_environment_identities")
        if not isinstance(environment, list):
            raise StatementReceiptReissueError(
                "current cache target has no dependency-environment receipt"
            )
        for raw_environment in environment:
            if not isinstance(raw_environment, Mapping):
                raise StatementReceiptReissueError(
                    "current cache target has a malformed dependency-environment receipt"
                )
            path = str(raw_environment.get("path") or "").strip()
            digest = _sha256(raw_environment.get("sha256"))
            if not path or not digest or control_by_path.get(path) != digest:
                raise StatementReceiptReissueError(
                    "current cache dependency environment differs from the source-record Lean closure"
                )
    return closure, _canonical_lean_import_closure_bytes(closure), closure_sha


def _historical_manifest_replay_plan_descriptor(
    plan: Mapping[str, Any],
    *,
    surface: CurrentReceiptSurface,
    receipt: object,
    receipt_bytes: bytes | None,
    artifact_path: str | None,
    historical_manifest_carrier: object,
    historical_manifest_carrier_bytes: bytes | None,
    historical_manifest_carrier_path: str | None,
    historical_manifest_authority: object,
    historical_manifest_authority_bytes: bytes | None,
    historical_manifest_authority_path: str | None,
    current_source_record_audit: object,
    current_source_record_audit_bytes: bytes | None,
    current_source_record_audit_path: str | None,
    prior_sidecar_archive_path: str | None,
    historical_manifest_store_recovery_receipt: object = None,
    historical_manifest_store_recovery_receipt_bytes: bytes | None = None,
    historical_manifest_store_recovery_receipt_path: str | None = None,
    historical_manifest_store_recovery_authority: object = None,
    historical_manifest_store_recovery_authority_bytes: bytes | None = None,
    historical_manifest_store_recovery_authority_path: str | None = None,
    historical_manifest_store_recovery_carrier_compressed_bytes: bytes | None = None,
    historical_manifest_store_recovery_carrier_compressed_path: str | None = None,
    current_source_record_authority_verifier: (
        HistoricalManifestReplayCurrentClosureAuthorityVerifier | None
    ) = None,
) -> HistoricalManifestReplayInputs:
    """Validate the plan's immutable reference to a replay artifact.

    The filesystem path is only a retrieval coordinate.  The plan also pins
    the raw bytes and the artifact's internal integrity digest, which are the
    evidence identities used below.
    """

    descriptor = plan.get(HISTORICAL_REPLAY_PLAN_FIELD)
    if not isinstance(descriptor, Mapping):
        raise StatementReceiptReissueError(
            "historical replay action requires a plan-pinned replay artifact descriptor"
        )
    legacy_expected_fields = {
        "artifact_path",
        "artifact_bytes_sha256",
        "replay_receipt_sha256",
        "historical_manifest_carrier_path",
        "historical_manifest_carrier_bytes_sha256",
        "historical_manifest_authority_path",
        "historical_manifest_authority_bytes_sha256",
        "current_source_record_audit_path",
        "current_source_record_audit_bytes_sha256",
        "prior_sidecar_archive_path",
    }
    recovered_store_expected_fields = {
        "artifact_path",
        "artifact_bytes_sha256",
        "replay_receipt_sha256",
        HISTORICAL_REPLAY_RECOVERED_STORE_FIELD,
        "current_source_record_audit_path",
        "current_source_record_audit_bytes_sha256",
        "prior_sidecar_archive_path",
    }
    descriptor_fields = set(descriptor)
    if descriptor_fields == legacy_expected_fields:
        uses_recovered_store = False
    elif descriptor_fields == recovered_store_expected_fields:
        uses_recovered_store = True
    else:
        raise StatementReceiptReissueError(
            "historical replay artifact descriptor has unsupported or missing fields"
        )
    planned_path, parsed, exact_bytes = _plan_pinned_historical_json_artifact(
        label="historical replay artifact",
        planned_path=descriptor.get("artifact_path"),
        planned_bytes_sha256=descriptor.get("artifact_bytes_sha256"),
        supplied_path=artifact_path,
        supplied_bytes=receipt_bytes,
        supplied_object=receipt,
    )
    expected_receipt_sha = _required_sha256(
        descriptor.get("replay_receipt_sha256"),
        label="historical replay replay_receipt_sha256",
    )
    recorded_receipt_sha = _sha256(
        parsed.get(
            historical_manifest_replay.HISTORICAL_STATEMENT_MANIFEST_REPLAY_INTEGRITY_FIELD
        )
    )
    if recorded_receipt_sha != expected_receipt_sha:
        raise StatementReceiptReissueError(
            "historical replay receipt integrity digest differs from the plan pin"
        )
    prior_archive_path = _normalized_paper_relative_path_text(
        descriptor.get("prior_sidecar_archive_path"),
        label="historical replay prior_sidecar_archive_path",
    )
    if prior_sidecar_archive_path != prior_archive_path:
        raise StatementReceiptReissueError(
            "historical replay prior-sidecar archive path does not equal the plan pin"
        )
    recovered_manifest_store: RecoveredManifestStoreInputs | None = None
    if uses_recovered_store:
        if any(
            value is not None
            for value in (
                historical_manifest_carrier,
                historical_manifest_carrier_bytes,
                historical_manifest_carrier_path,
                historical_manifest_authority,
                historical_manifest_authority_bytes,
                historical_manifest_authority_path,
            )
        ):
            raise StatementReceiptReissueError(
                "recovered historical manifest-store replay cannot mix uncompressed carrier inputs"
            )
        (
            recovered_manifest_store,
            parsed_authority,
            parsed_carrier,
            exact_carrier_bytes,
        ) = _verified_recovered_manifest_store_bundle(
            paper=surface.paper,
            descriptor=descriptor.get(HISTORICAL_REPLAY_RECOVERED_STORE_FIELD),
            recovery_receipt=historical_manifest_store_recovery_receipt,
            recovery_receipt_bytes=historical_manifest_store_recovery_receipt_bytes,
            recovery_receipt_path=historical_manifest_store_recovery_receipt_path,
            authority=historical_manifest_store_recovery_authority,
            authority_bytes=historical_manifest_store_recovery_authority_bytes,
            authority_path=historical_manifest_store_recovery_authority_path,
            carrier_compressed_bytes=(
                historical_manifest_store_recovery_carrier_compressed_bytes
            ),
            carrier_compressed_path=(
                historical_manifest_store_recovery_carrier_compressed_path
            ),
            label="historical replay recovered manifest store",
        )
        carrier_path: str | None = None
        authority_path: str | None = None
        exact_authority_bytes = recovered_manifest_store.authority_bytes
    else:
        if any(
            value is not None
            for value in (
                historical_manifest_store_recovery_receipt,
                historical_manifest_store_recovery_receipt_bytes,
                historical_manifest_store_recovery_receipt_path,
                historical_manifest_store_recovery_authority,
                historical_manifest_store_recovery_authority_bytes,
                historical_manifest_store_recovery_authority_path,
                historical_manifest_store_recovery_carrier_compressed_bytes,
                historical_manifest_store_recovery_carrier_compressed_path,
            )
        ):
            raise StatementReceiptReissueError(
                "uncompressed historical manifest replay cannot mix recovered-store inputs"
            )
        carrier_path, parsed_carrier, exact_carrier_bytes = (
            _plan_pinned_historical_json_artifact(
                label="historical replay manifest carrier",
                planned_path=descriptor.get("historical_manifest_carrier_path"),
                planned_bytes_sha256=descriptor.get(
                    "historical_manifest_carrier_bytes_sha256"
                ),
                supplied_path=historical_manifest_carrier_path,
                supplied_bytes=historical_manifest_carrier_bytes,
                supplied_object=historical_manifest_carrier,
            )
        )
        authority_path, parsed_authority, exact_authority_bytes = (
            _plan_pinned_historical_json_artifact(
                label="historical replay manifest authority",
                planned_path=descriptor.get("historical_manifest_authority_path"),
                planned_bytes_sha256=descriptor.get(
                    "historical_manifest_authority_bytes_sha256"
                ),
                supplied_path=historical_manifest_authority_path,
                supplied_bytes=historical_manifest_authority_bytes,
                supplied_object=historical_manifest_authority,
            )
        )
    source_record_path, parsed_source_record, exact_source_record_bytes = (
        _plan_pinned_historical_json_artifact(
            label="historical replay current source-record audit",
            planned_path=descriptor.get("current_source_record_audit_path"),
            planned_bytes_sha256=descriptor.get(
                "current_source_record_audit_bytes_sha256"
            ),
            supplied_path=current_source_record_audit_path,
            supplied_bytes=current_source_record_audit_bytes,
            supplied_object=current_source_record_audit,
        )
    )
    authority_verifier = (
        current_source_record_authority_verifier
        or _validated_current_source_record_closure_authority
    )
    try:
        closure, closure_bytes, closure_sha = authority_verifier(
            surface, parsed_source_record
        )
    except StatementReceiptReissueError:
        raise
    except Exception as exc:  # pragma: no cover - defensive test-seam boundary.
        raise StatementReceiptReissueError(
            "current source-record closure authority verifier raised "
            f"{type(exc).__name__}"
        ) from exc
    if not isinstance(closure, Mapping) or not isinstance(closure_bytes, bytes):
        raise StatementReceiptReissueError(
            "current source-record closure authority verifier returned malformed closure evidence"
        )
    if _sha256(closure_sha) != closure_sha:
        raise StatementReceiptReissueError(
            "current source-record closure authority verifier returned an invalid closure digest"
        )
    return HistoricalManifestReplayInputs(
        descriptor=dict(descriptor),
        receipt=parsed,
        receipt_bytes=exact_bytes,
        receipt_path=planned_path,
        carrier=parsed_carrier,
        carrier_bytes=exact_carrier_bytes,
        carrier_path=carrier_path,
        authority=parsed_authority,
        authority_bytes=exact_authority_bytes,
        authority_path=authority_path,
        current_source_record_audit=parsed_source_record,
        current_source_record_audit_bytes=exact_source_record_bytes,
        current_source_record_audit_path=source_record_path,
        current_lean_import_closure=closure,
        current_lean_import_closure_bytes=closure_bytes,
        current_lean_import_closure_sha256=closure_sha,
        prior_sidecar_archive_path=prior_archive_path,
        recovered_manifest_store=recovered_manifest_store,
    )


def _historical_manifest_replay_recipe_verifier_error(
    verifier: HistoricalManifestReplayRecipeVerifier | None,
    recipe: Mapping[str, object],
) -> str:
    """Run the injected no-Lean verifier for an artifact's exact recipe.

    Static replay validation can establish that a receipt is self-consistent,
    but it cannot itself prove that the recipe's Git object ids refer to real
    repository objects.  Production injects ``runner.verify_recipe`` here;
    that runner verifies the historical commit/blob tree and current file pins
    without invoking the historical Lean serializer.
    """

    if verifier is None or not callable(verifier):
        return "a static historical recipe verifier is required"
    try:
        outcome = verifier(copy.deepcopy(dict(recipe)))
    except Exception as exc:  # pragma: no cover - defensive callback boundary.
        return f"historical recipe verifier raised {type(exc).__name__}"
    if outcome is None or outcome == "":
        return ""
    if isinstance(outcome, str):
        return outcome
    return "historical recipe verifier must return an error string or None"


def _validated_historical_manifest_replay(
    surface: CurrentReceiptSurface,
    prior: PriorSidecar,
    plan: Mapping[str, Any],
    *,
    receipt: object,
    receipt_bytes: bytes | None,
    artifact_path: str | None,
    historical_manifest_carrier: object,
    historical_manifest_carrier_bytes: bytes | None,
    historical_manifest_carrier_path: str | None,
    historical_manifest_authority: object,
    historical_manifest_authority_bytes: bytes | None,
    historical_manifest_authority_path: str | None,
    current_source_record_audit: object,
    current_source_record_audit_bytes: bytes | None,
    current_source_record_audit_path: str | None,
    prior_sidecar_archive_path: str | None,
    recipe_verifier: HistoricalManifestReplayRecipeVerifier | None,
    current_source_record_authority_verifier: (
        HistoricalManifestReplayCurrentClosureAuthorityVerifier | None
    ) = None,
    historical_manifest_store_recovery_receipt: object = None,
    historical_manifest_store_recovery_receipt_bytes: bytes | None = None,
    historical_manifest_store_recovery_receipt_path: str | None = None,
    historical_manifest_store_recovery_authority: object = None,
    historical_manifest_store_recovery_authority_bytes: bytes | None = None,
    historical_manifest_store_recovery_authority_path: str | None = None,
    historical_manifest_store_recovery_carrier_compressed_bytes: bytes | None = None,
    historical_manifest_store_recovery_carrier_compressed_path: str | None = None,
) -> tuple[
    historical_manifest_replay.ValidatedHistoricalStatementManifestReplay,
    HistoricalManifestReplayInputs,
]:
    """Statically validate one plan-pinned historic serializer bridge.

    This intentionally calls the bridge's normal static validator, never its
    explicit strong replay path.  Materialization must not re-elaborate Lean
    or repeat a historical serializer invocation just to copy a receipt.
    """

    if not prior.present:
        raise StatementReceiptReissueError(
            "historical replay action names an absent prior statement sidecar"
        )
    replay_inputs = _historical_manifest_replay_plan_descriptor(
        plan,
        surface=surface,
        receipt=receipt,
        receipt_bytes=receipt_bytes,
        artifact_path=artifact_path,
        historical_manifest_carrier=historical_manifest_carrier,
        historical_manifest_carrier_bytes=historical_manifest_carrier_bytes,
        historical_manifest_carrier_path=historical_manifest_carrier_path,
        historical_manifest_authority=historical_manifest_authority,
        historical_manifest_authority_bytes=historical_manifest_authority_bytes,
        historical_manifest_authority_path=historical_manifest_authority_path,
        current_source_record_audit=current_source_record_audit,
        current_source_record_audit_bytes=current_source_record_audit_bytes,
        current_source_record_audit_path=current_source_record_audit_path,
        prior_sidecar_archive_path=prior_sidecar_archive_path,
        historical_manifest_store_recovery_receipt=(
            historical_manifest_store_recovery_receipt
        ),
        historical_manifest_store_recovery_receipt_bytes=(
            historical_manifest_store_recovery_receipt_bytes
        ),
        historical_manifest_store_recovery_receipt_path=(
            historical_manifest_store_recovery_receipt_path
        ),
        historical_manifest_store_recovery_authority=(
            historical_manifest_store_recovery_authority
        ),
        historical_manifest_store_recovery_authority_bytes=(
            historical_manifest_store_recovery_authority_bytes
        ),
        historical_manifest_store_recovery_authority_path=(
            historical_manifest_store_recovery_authority_path
        ),
        historical_manifest_store_recovery_carrier_compressed_bytes=(
            historical_manifest_store_recovery_carrier_compressed_bytes
        ),
        historical_manifest_store_recovery_carrier_compressed_path=(
            historical_manifest_store_recovery_carrier_compressed_path
        ),
        current_source_record_authority_verifier=(
            current_source_record_authority_verifier
        ),
    )
    recipe = replay_inputs.receipt.get("historical_serializer_recipe")
    if not isinstance(recipe, Mapping):
        raise StatementReceiptReissueError(
            "historical replay artifact has no serializer recipe"
        )
    if verifier_error := _historical_manifest_replay_recipe_verifier_error(
        recipe_verifier, recipe
    ):
        raise StatementReceiptReissueError(
            "historical replay recipe is not independently verified: "
            + verifier_error
        )
    targets = historical_manifest_replay_current_targets(surface)
    context, error = historical_manifest_replay.validate_historical_statement_manifest_replay(
        replay_inputs.receipt,
        paper=surface.paper,
        historical_serializer_recipe=dict(recipe),
        prior_sidecar=prior.payload,
        prior_sidecar_bytes=prior.raw_bytes,
        historical_manifest_carrier=replay_inputs.carrier,
        historical_manifest_carrier_bytes=replay_inputs.carrier_bytes,
        historical_manifest_authority=replay_inputs.authority,
        historical_manifest_authority_bytes=replay_inputs.authority_bytes,
        current_targets=targets,
        current_evidence_sha256=historical_manifest_replay_current_evidence_sha256(
            surface
        ),
        current_target_validator=lambda raw: _historical_manifest_replay_target_validator(
            surface, raw
        ),
        source_route_validator=lambda raw: _historical_manifest_replay_source_route_validator(
            surface, raw
        ),
    )
    if error or context is None:
        raise StatementReceiptReissueError(
            "historical replay artifact is not current static evidence"
            + (f": {error}" if error else "")
        )
    return context, replay_inputs


_PERSISTED_HISTORICAL_REPLAY_LEGACY_PROVENANCE_FIELDS = frozenset(
    {
        "schema",
        "artifact_kind",
        "policy_version",
        "replay_artifact_path",
        "replay_artifact_bytes_sha256",
        "historical_statement_manifest_replay_sha256",
        "historical_manifest_carrier_path",
        "historical_manifest_carrier_bytes_sha256",
        "historical_manifest_authority_path",
        "historical_manifest_authority_bytes_sha256",
        "current_source_record_audit_path",
        "current_source_record_audit_bytes_sha256",
        "current_lean_import_closure_sha256",
        "prior_sidecar_archive_path",
        "prior_sidecar_bytes_sha256",
        "prior_entry_payload_sha256",
        "historical_pair_sha256",
        "atom_transport_sha256",
        "current_semantic_target_sha256",
        "current_surface_sha256",
        "current_source_route_inventory_sha256",
    }
)
_PERSISTED_HISTORICAL_REPLAY_RECOVERED_STORE_PROVENANCE_FIELDS = frozenset(
    (
        _PERSISTED_HISTORICAL_REPLAY_LEGACY_PROVENANCE_FIELDS
        - {
            "historical_manifest_carrier_path",
            "historical_manifest_carrier_bytes_sha256",
            "historical_manifest_authority_path",
            "historical_manifest_authority_bytes_sha256",
        }
    )
    | {HISTORICAL_REPLAY_RECOVERED_STORE_FIELD}
)
# Kept as a compatibility name for callers/tests that inspect the v1 receipt
# shape directly.  New recovered-store receipts use the explicit v2 set above.
_PERSISTED_HISTORICAL_REPLAY_PROVENANCE_FIELDS = (
    _PERSISTED_HISTORICAL_REPLAY_LEGACY_PROVENANCE_FIELDS
)


def _persisted_historical_replay_json_artifact(
    folder: Path,
    *,
    path_text: object,
    expected_sha256: object,
    label: str,
) -> tuple[Path, str, dict[str, Any], bytes]:
    """Load one persisted replay input by coordinate and exact-byte digest."""

    relative = _normalized_paper_relative_path_text(path_text, label=f"{label} path")
    expected = _required_sha256(expected_sha256, label=f"{label} bytes_sha256")
    try:
        path = _paper_relative_path(Path(relative), folder, label=f"{label} path")
        raw = path.read_bytes()
    except OSError as exc:
        raise StatementReceiptReissueError(f"{label} is unavailable") from exc
    if _bytes_sha256(raw) != expected:
        raise StatementReceiptReissueError(f"{label} bytes differ from its provenance pin")
    return path, relative, _read_json_object(raw, label=label), raw


def _persisted_historical_replay_bytes_artifact(
    folder: Path,
    *,
    path_text: object,
    expected_sha256: object,
    label: str,
) -> tuple[Path, str, bytes]:
    """Reopen a pinned opaque replay artifact without decoding it."""

    relative = _normalized_paper_relative_path_text(path_text, label=f"{label} path")
    expected = _required_sha256(expected_sha256, label=f"{label} bytes_sha256")
    try:
        path = _paper_relative_path(Path(relative), folder, label=f"{label} path")
        raw = path.read_bytes()
    except OSError as exc:
        raise StatementReceiptReissueError(f"{label} is unavailable") from exc
    if _bytes_sha256(raw) != expected:
        raise StatementReceiptReissueError(f"{label} bytes differ from its provenance pin")
    return path, relative, raw


def historical_manifest_replay_persisted_evidence_errors(folder: Path) -> list[str]:
    """Validate every persisted historic-manifest transport without Lean.

    This is the post-materialization evidence gate.  It reopens each named
    artifact only by its persisted paper-relative coordinate and raw-byte
    digest, authenticates the old semantic closure and current source-record
    closure, verifies the Git/current-file recipe statically, and reconstructs
    the exact ordinary statement receipt.  It intentionally never invokes the
    historical serializer or resolves a target by its declaration spelling.
    """

    sidecar_path = folder / "audit" / "statement_match_llm.json"
    try:
        sidecar_raw = sidecar_path.read_bytes()
        sidecar = _read_json_object(sidecar_raw, label="current statement sidecar")
    except (OSError, ValueError, StatementReceiptReissueError) as exc:
        return [f"could not load current statement sidecar: {exc}"]
    items = sidecar.get("items")
    if not isinstance(items, Mapping):
        return ["current statement sidecar has no object-valued items"]
    transport_entries = [
        (str(storage_key), entry, entry.get(HISTORICAL_REPLAY_PROVENANCE_FIELD))
        for storage_key, entry in items.items()
        if isinstance(entry, Mapping)
        and HISTORICAL_REPLAY_PROVENANCE_FIELD in entry
    ]
    if not transport_entries:
        return []

    try:
        surface = current_statement_receipt_surface(folder)
    except (OSError, ValueError, StatementReceiptReissueError) as exc:
        return [f"could not load current receipt surface: {exc}"]
    targets = {target.semantic_target_sha256: target for target in surface.targets}
    errors: list[str] = []
    opened_bytes: dict[Path, bytes] = {sidecar_path.resolve(): sidecar_raw}

    for storage_key, raw_entry, raw_provenance in transport_entries:
        label = f"historical replay sidecar item {storage_key!r}"
        if not isinstance(raw_provenance, Mapping):
            errors.append(f"{label} provenance is not an object")
            continue
        provenance = dict(raw_provenance)
        policy_version = provenance.get("policy_version")
        if policy_version == HISTORICAL_REPLAY_PROVENANCE_POLICY_VERSION:
            uses_recovered_store = False
            expected_fields = _PERSISTED_HISTORICAL_REPLAY_LEGACY_PROVENANCE_FIELDS
        elif policy_version == HISTORICAL_REPLAY_RECOVERED_STORE_PROVENANCE_POLICY_VERSION:
            uses_recovered_store = True
            expected_fields = (
                _PERSISTED_HISTORICAL_REPLAY_RECOVERED_STORE_PROVENANCE_FIELDS
            )
        else:
            errors.append(f"{label} provenance has an unsupported schema or policy")
            continue
        if (
            set(provenance) != expected_fields
            or provenance.get("schema") != HISTORICAL_REPLAY_PROVENANCE_SCHEMA
            or provenance.get("artifact_kind") != HISTORICAL_REPLAY_PROVENANCE_KIND
        ):
            errors.append(f"{label} provenance has unsupported or missing fields")
            continue
        try:
            bridge_path, bridge_relative, bridge, bridge_bytes = (
                _persisted_historical_replay_json_artifact(
                    folder,
                    path_text=provenance.get("replay_artifact_path"),
                    expected_sha256=provenance.get("replay_artifact_bytes_sha256"),
                    label=f"{label} replay artifact",
                )
            )
            recovered_manifest_store: RecoveredManifestStoreInputs | None = None
            if uses_recovered_store:
                recovered_metadata = _recovered_manifest_store_metadata(
                    provenance.get(HISTORICAL_REPLAY_RECOVERED_STORE_FIELD),
                    label=f"{label} recovered manifest store",
                )
                (
                    recovery_receipt_path,
                    recovery_receipt_relative,
                    recovery_receipt,
                    recovery_receipt_bytes,
                ) = _persisted_historical_replay_json_artifact(
                    folder,
                    path_text=recovered_metadata["recovery_receipt_path"],
                    expected_sha256=recovered_metadata[
                        "recovery_receipt_bytes_sha256"
                    ],
                    label=f"{label} recovered manifest-store receipt",
                )
                (
                    authority_path,
                    authority_relative,
                    raw_authority,
                    authority_bytes,
                ) = _persisted_historical_replay_json_artifact(
                    folder,
                    path_text=recovered_metadata["authority_path"],
                    expected_sha256=recovered_metadata["authority_bytes_sha256"],
                    label=f"{label} recovered manifest-store authority",
                )
                carrier_path, carrier_relative, carrier_compressed_bytes = (
                    _persisted_historical_replay_bytes_artifact(
                        folder,
                        path_text=recovered_metadata["carrier_compressed_path"],
                        expected_sha256=recovered_metadata[
                            "carrier_compressed_bytes_sha256"
                        ],
                        label=f"{label} recovered manifest-store compressed carrier",
                    )
                )
                (
                    recovered_manifest_store,
                    authority,
                    carrier,
                    carrier_bytes,
                ) = _verified_recovered_manifest_store_bundle(
                    paper=surface.paper,
                    descriptor=recovered_metadata,
                    recovery_receipt=recovery_receipt,
                    recovery_receipt_bytes=recovery_receipt_bytes,
                    recovery_receipt_path=recovery_receipt_relative,
                    authority=raw_authority,
                    authority_bytes=authority_bytes,
                    authority_path=authority_relative,
                    carrier_compressed_bytes=carrier_compressed_bytes,
                    carrier_compressed_path=carrier_relative,
                    label=f"{label} recovered manifest store",
                )
                raw_store_paths = (
                    (recovery_receipt_path, recovery_receipt_bytes),
                    (authority_path, authority_bytes),
                    (carrier_path, carrier_compressed_bytes),
                )
            else:
                carrier_path, _carrier_relative, carrier, carrier_bytes = (
                    _persisted_historical_replay_json_artifact(
                        folder,
                        path_text=provenance.get("historical_manifest_carrier_path"),
                        expected_sha256=provenance.get(
                            "historical_manifest_carrier_bytes_sha256"
                        ),
                        label=f"{label} historical manifest carrier",
                    )
                )
                authority_path, _authority_relative, authority, authority_bytes = (
                    _persisted_historical_replay_json_artifact(
                        folder,
                        path_text=provenance.get("historical_manifest_authority_path"),
                        expected_sha256=provenance.get(
                            "historical_manifest_authority_bytes_sha256"
                        ),
                        label=f"{label} historical manifest authority",
                    )
                )
                raw_store_paths = (
                    (carrier_path, carrier_bytes),
                    (authority_path, authority_bytes),
                )
            source_record_path, _source_record_relative, source_record, source_record_bytes = (
                _persisted_historical_replay_json_artifact(
                    folder,
                    path_text=provenance.get("current_source_record_audit_path"),
                    expected_sha256=provenance.get(
                        "current_source_record_audit_bytes_sha256"
                    ),
                    label=f"{label} current source-record audit",
                )
            )
            for path, raw in (
                (bridge_path, bridge_bytes),
                *raw_store_paths,
                (source_record_path, source_record_bytes),
            ):
                prior_raw = opened_bytes.setdefault(path.resolve(), raw)
                if prior_raw != raw:
                    raise StatementReceiptReissueError(
                        f"{label} reuses one artifact path with inconsistent bytes"
                    )
            closure, closure_bytes, closure_sha = (
                _validated_current_source_record_closure_authority(
                    surface, source_record
                )
            )
            if closure_sha != _required_sha256(
                provenance.get("current_lean_import_closure_sha256"),
                label=f"{label} provenance current_lean_import_closure_sha256",
            ):
                raise StatementReceiptReissueError(
                    f"{label} source-record Lean closure differs from its provenance pin"
                )
            recipe = bridge.get("historical_serializer_recipe")
            if not isinstance(recipe, Mapping):
                raise StatementReceiptReissueError(
                    f"{label} replay artifact has no historical serializer recipe"
                )
            recipe_verifier = _historical_manifest_replay_cli_recipe_verifier(
                root=ROOT,
                paper_dir=folder,
                current_lean_import_closure=closure,
                current_lean_import_closure_bytes=closure_bytes,
            )
            if recipe_error := _historical_manifest_replay_recipe_verifier_error(
                recipe_verifier, recipe
            ):
                raise StatementReceiptReissueError(
                    f"{label} recipe is not independently verified: {recipe_error}"
                )
            archive_relative = _normalized_paper_relative_path_text(
                provenance.get("prior_sidecar_archive_path"),
                label=f"{label} prior-sidecar archive path",
            )
            archive_path = _paper_relative_path(
                Path(archive_relative), folder, label=f"{label} prior-sidecar archive path"
            )
            try:
                archive_raw = archive_path.read_bytes()
                archive = _read_json_object(archive_raw, label=f"{label} prior-sidecar archive")
            except OSError as exc:
                raise StatementReceiptReissueError(
                    f"{label} prior-sidecar archive is unavailable"
                ) from exc
            prior_raw = opened_bytes.setdefault(archive_path.resolve(), archive_raw)
            if prior_raw != archive_raw:
                raise StatementReceiptReissueError(
                    f"{label} reuses one prior-sidecar archive path with inconsistent bytes"
                )
            if (
                archive.get("schema") != REISSUE_SCHEMA
                or archive.get("artifact_kind") != ARCHIVE_KIND
                or archive.get("policy_version") != POLICY_VERSION
                or archive.get("paper") != surface.paper
            ):
                raise StatementReceiptReissueError(
                    f"{label} prior-sidecar archive has unsupported identity"
                )
            encoded_prior = archive.get("prior_sidecar_bytes_base64")
            if not isinstance(encoded_prior, str):
                raise StatementReceiptReissueError(
                    f"{label} prior-sidecar archive has no exact prior bytes"
                )
            try:
                archived_prior_bytes = base64.b64decode(encoded_prior, validate=True)
            except ValueError as exc:
                raise StatementReceiptReissueError(
                    f"{label} prior-sidecar archive has malformed base64"
                ) from exc
            if _bytes_sha256(archived_prior_bytes) != _required_sha256(
                archive.get("prior_sidecar_sha256"),
                label=f"{label} archive prior_sidecar_sha256",
            ):
                raise StatementReceiptReissueError(
                    f"{label} prior-sidecar archive bytes do not match its own pin"
                )
            if _bytes_sha256(archived_prior_bytes) != _required_sha256(
                provenance.get("prior_sidecar_bytes_sha256"),
                label=f"{label} provenance prior_sidecar_bytes_sha256",
            ):
                raise StatementReceiptReissueError(
                    f"{label} prior-sidecar archive differs from its provenance pin"
                )
            prior = _prior_sidecar_from_raw(
                archived_prior_bytes, label=f"{label} archived prior statement sidecar"
            )
            target_id = _required_sha256(
                provenance.get("current_semantic_target_sha256"),
                label=f"{label} provenance current_semantic_target_sha256",
            )
            target = targets.get(target_id)
            if target is None:
                raise StatementReceiptReissueError(
                    f"{label} current semantic target is absent"
                )
            context, replay_error = (
                historical_manifest_replay.validate_historical_statement_manifest_replay(
                    bridge,
                    paper=surface.paper,
                    historical_serializer_recipe=dict(recipe),
                    prior_sidecar=prior.payload,
                    prior_sidecar_bytes=prior.raw_bytes,
                    historical_manifest_carrier=carrier,
                    historical_manifest_carrier_bytes=carrier_bytes,
                    historical_manifest_authority=authority,
                    historical_manifest_authority_bytes=authority_bytes,
                    current_targets=historical_manifest_replay_current_targets(surface),
                    current_evidence_sha256=(
                        historical_manifest_replay_current_evidence_sha256(surface)
                    ),
                    current_target_validator=(
                        lambda raw: _historical_manifest_replay_target_validator(
                            surface, raw
                        )
                    ),
                    source_route_validator=(
                        lambda raw: _historical_manifest_replay_source_route_validator(
                            surface, raw
                        )
                    ),
                )
            )
            if replay_error or context is None:
                raise StatementReceiptReissueError(
                    f"{label} replay artifact is not current static evidence"
                    + (f": {replay_error}" if replay_error else "")
                )
            receipt_sha = _required_sha256(
                provenance.get("historical_statement_manifest_replay_sha256"),
                label=f"{label} provenance historical_statement_manifest_replay_sha256",
            )
            if context.receipt_sha256 != receipt_sha:
                raise StatementReceiptReissueError(
                    f"{label} replay receipt differs from its provenance pin"
                )
            prior_payload_sha = _required_sha256(
                provenance.get("prior_entry_payload_sha256"),
                label=f"{label} provenance prior_entry_payload_sha256",
            )
            prior_entries = prior.groups.get(prior_payload_sha)
            if not prior_entries or len(prior_entries) != 1:
                raise StatementReceiptReissueError(
                    f"{label} archived prior payload is not a unique evidence object"
                )
            binding = historical_manifest_replay.replay_binding_for_current_target(
                context,
                prior_entry_payload_sha256=prior_payload_sha,
                current_identity=target.identity,
            )
            if binding is None:
                raise StatementReceiptReissueError(
                    f"{label} has no exact historic/current content binding"
                )
            expected_entry = _historical_manifest_replay_transport_entry(
                prior_entries[0],
                binding=binding,
                target=target,
                surface=surface,
                prior=prior,
                replay_artifact_path=bridge_relative,
                prior_payload_sha256=prior_payload_sha,
                replay_artifact_bytes_sha256=_bytes_sha256(bridge_bytes),
                replay_receipt_sha256=receipt_sha,
                historical_manifest_carrier_path=(
                    None
                    if uses_recovered_store
                    else _normalized_paper_relative_path_text(
                        provenance.get("historical_manifest_carrier_path"),
                        label=f"{label} provenance historical_manifest_carrier_path",
                    )
                ),
                historical_manifest_carrier_bytes_sha256=(
                    None if uses_recovered_store else _bytes_sha256(carrier_bytes)
                ),
                historical_manifest_authority_path=(
                    None
                    if uses_recovered_store
                    else _normalized_paper_relative_path_text(
                        provenance.get("historical_manifest_authority_path"),
                        label=f"{label} provenance historical_manifest_authority_path",
                    )
                ),
                historical_manifest_authority_bytes_sha256=(
                    None if uses_recovered_store else _bytes_sha256(authority_bytes)
                ),
                current_source_record_audit_path=_normalized_paper_relative_path_text(
                    provenance.get("current_source_record_audit_path"),
                    label=f"{label} provenance current_source_record_audit_path",
                ),
                current_source_record_audit_bytes_sha256=_bytes_sha256(
                    source_record_bytes
                ),
                current_lean_import_closure_sha256=closure_sha,
                prior_sidecar_archive_path=archive_relative,
                recovered_manifest_store=recovered_manifest_store,
            )
            if dict(raw_entry) != expected_entry:
                raise StatementReceiptReissueError(
                    f"{label} does not equal its deterministic transported receipt"
                )
            records = archive.get("historical_statement_manifest_replay_transports")
            if not isinstance(records, list) or not any(
                isinstance(record, Mapping) and dict(record) == provenance
                for record in records
            ):
                raise StatementReceiptReissueError(
                    f"{label} provenance is absent from its exact prior-sidecar archive"
                )
        except StatementReceiptReissueError as exc:
            errors.append(str(exc))
        except Exception as exc:  # noqa: BLE001 - malformed persisted evidence fails closed.
            errors.append(f"{label} validation raised {type(exc).__name__}")

    # A committed sidecar is not evidence if its retrieval coordinates changed
    # while this static gate was reading them.  The current receipt surface has
    # its own before/after cache/map protection; repeat that content comparison
    # once here and avoid a historical Lean invocation.
    for path, raw in opened_bytes.items():
        try:
            if path.read_bytes() != raw:
                errors.append(
                    f"persisted historical replay input changed during validation: {path}"
                )
        except OSError:
            errors.append(
                f"persisted historical replay input became unavailable during validation: {path}"
            )
    try:
        final_surface = current_statement_receipt_surface(folder)
    except (OSError, ValueError, StatementReceiptReissueError) as exc:
        errors.append(f"current receipt surface became unavailable during validation: {exc}")
    else:
        if not _same_surface(surface, final_surface):
            errors.append("current receipt surface changed during historical replay validation")
    return errors


def _historical_manifest_replay_transport_entry(
    entry: Mapping[str, Any],
    *,
    binding: Mapping[str, object],
    target: CurrentReceiptTarget,
    surface: CurrentReceiptSurface,
    prior: PriorSidecar,
    replay_artifact_path: str,
    prior_payload_sha256: str,
    replay_artifact_bytes_sha256: str,
    replay_receipt_sha256: str,
    historical_manifest_carrier_path: str | None,
    historical_manifest_carrier_bytes_sha256: str | None,
    historical_manifest_authority_path: str | None,
    historical_manifest_authority_bytes_sha256: str | None,
    current_source_record_audit_path: str,
    current_source_record_audit_bytes_sha256: str,
    current_lean_import_closure_sha256: str,
    prior_sidecar_archive_path: str,
    recovered_manifest_store: RecoveredManifestStoreInputs | None = None,
) -> dict[str, Any]:
    """Apply one validated old-ref/current-ref atom transport to a receipt."""

    historical_signature = _required_sha256(
        binding.get("historical_manifest_signature_sha256"),
        label="historical replay binding historical_manifest_signature_sha256",
    )
    if _sha256(entry.get("lean_signature_sha256")) != historical_signature:
        raise StatementReceiptReissueError(
            "historical replay binding does not match the archived Lean signature"
        )
    if _entry_semantic_identity(entry) is None:
        raise StatementReceiptReissueError(
            "historical replay archived payload has no complete statement identity"
        )
    transport = binding.get("atom_transport")
    if not isinstance(transport, list) or not transport:
        raise StatementReceiptReissueError(
            "historical replay binding has no explicit atom transport"
        )
    transport_by_historical_ref: dict[str, dict[str, str]] = {}
    current_refs: set[str] = set()
    for raw_transport in transport:
        if not isinstance(raw_transport, Mapping):
            raise StatementReceiptReissueError(
                "historical replay binding has a non-object atom transport"
            )
        historical_ref = _required_text(
            raw_transport.get("historical_signature_ref"),
            label="historical replay historical_signature_ref",
        )
        current_ref = _required_text(
            raw_transport.get("current_signature_ref"),
            label="historical replay current_signature_ref",
        )
        historical_role = _required_text(
            raw_transport.get("historical_role"),
            label="historical replay historical_role",
        ).lower()
        current_role = _required_text(
            raw_transport.get("current_role"),
            label="historical replay current_role",
        ).lower()
        historical_atom_sha = _required_sha256(
            raw_transport.get("historical_signature_atom_sha256"),
            label="historical replay historical_signature_atom_sha256",
        )
        current_atom_sha = _required_sha256(
            raw_transport.get("current_signature_atom_sha256"),
            label="historical replay current_signature_atom_sha256",
        )
        if (
            historical_ref in transport_by_historical_ref
            or current_ref in current_refs
            or historical_role != current_role
            or historical_role not in {"parameter", "assumption", "conclusion"}
        ):
            raise StatementReceiptReissueError(
                "historical replay atom transport is not a one-to-one role-preserving map"
            )
        transport_by_historical_ref[historical_ref] = {
            "role": historical_role,
            "historical_signature_atom_sha256": historical_atom_sha,
            "current_signature_ref": current_ref,
            "current_signature_atom_sha256": current_atom_sha,
        }
        current_refs.add(current_ref)

    out = copy.deepcopy(dict(entry))
    obligations = out.get("lean_obligations")
    if not isinstance(obligations, list) or not obligations:
        raise StatementReceiptReissueError(
            "historical replay archived payload has no Lean obligations"
        )
    seen_historical_refs: set[str] = set()
    for obligation in obligations:
        if not isinstance(obligation, dict):
            raise StatementReceiptReissueError(
                "historical replay archived payload has a non-object Lean obligation"
            )
        historical_ref = _required_text(
            obligation.get("signature_ref"),
            label="historical replay archived signature_ref",
        )
        transport_row = transport_by_historical_ref.get(historical_ref)
        if transport_row is None or historical_ref in seen_historical_refs:
            raise StatementReceiptReissueError(
                "historical replay archived Lean obligations do not exactly match its transport"
            )
        if (
            _required_text(
                obligation.get("kind"), label="historical replay archived Lean obligation kind"
            ).lower()
            != transport_row["role"]
            or _sha256(obligation.get("signature_atom_sha256"))
            != transport_row["historical_signature_atom_sha256"]
        ):
            raise StatementReceiptReissueError(
                "historical replay archived Lean obligation differs from its historical atom pin"
            )
        obligation["signature_ref"] = transport_row["current_signature_ref"]
        obligation["signature_atom_sha256"] = transport_row[
            "current_signature_atom_sha256"
        ]
        seen_historical_refs.add(historical_ref)
    if seen_historical_refs != set(transport_by_historical_ref):
        raise StatementReceiptReissueError(
            "historical replay transport does not cover every archived Lean obligation"
        )

    out.update(
        {
            "lean_statement_sha256": target.lean_statement_sha256,
            **target.identity,
        }
    )
    out.pop(HISTORICAL_REPLAY_PROVENANCE_FIELD, None)
    provenance: dict[str, Any] = {
        "schema": HISTORICAL_REPLAY_PROVENANCE_SCHEMA,
        "artifact_kind": HISTORICAL_REPLAY_PROVENANCE_KIND,
        "replay_artifact_path": _normalized_paper_relative_path_text(
            replay_artifact_path,
            label="historical replay provenance replay_artifact_path",
        ),
        "replay_artifact_bytes_sha256": _required_sha256(
            replay_artifact_bytes_sha256,
            label="historical replay provenance replay_artifact_bytes_sha256",
        ),
        "historical_statement_manifest_replay_sha256": _required_sha256(
            replay_receipt_sha256,
            label="historical replay provenance historical_statement_manifest_replay_sha256",
        ),
        "current_source_record_audit_path": _normalized_paper_relative_path_text(
            current_source_record_audit_path,
            label="historical replay provenance current_source_record_audit_path",
        ),
        "current_source_record_audit_bytes_sha256": _required_sha256(
            current_source_record_audit_bytes_sha256,
            label="historical replay provenance current_source_record_audit_bytes_sha256",
        ),
        "current_lean_import_closure_sha256": _required_sha256(
            current_lean_import_closure_sha256,
            label="historical replay provenance current_lean_import_closure_sha256",
        ),
        "prior_sidecar_archive_path": _normalized_paper_relative_path_text(
            prior_sidecar_archive_path,
            label="historical replay provenance prior_sidecar_archive_path",
        ),
        "prior_sidecar_bytes_sha256": prior.raw_sha256,
        "prior_entry_payload_sha256": prior_payload_sha256,
        "historical_pair_sha256": _required_sha256(
            binding.get("historical_pair_sha256"),
            label="historical replay binding historical_pair_sha256",
        ),
        "atom_transport_sha256": _digest(transport),
        "current_semantic_target_sha256": target.semantic_target_sha256,
        "current_surface_sha256": surface.current_surface_sha256,
        "current_source_route_inventory_sha256": surface.source_route_inventory_sha256,
    }
    if recovered_manifest_store is not None:
        if any(
            value is not None
            for value in (
                historical_manifest_carrier_path,
                historical_manifest_carrier_bytes_sha256,
                historical_manifest_authority_path,
                historical_manifest_authority_bytes_sha256,
            )
        ):
            raise StatementReceiptReissueError(
                "recovered-store transport cannot also record uncompressed carrier pins"
            )
        provenance["policy_version"] = (
            HISTORICAL_REPLAY_RECOVERED_STORE_PROVENANCE_POLICY_VERSION
        )
        provenance[HISTORICAL_REPLAY_RECOVERED_STORE_FIELD] = {
            "recovery_receipt_path": _normalized_paper_relative_path_text(
                recovered_manifest_store.recovery_receipt_path,
                label="historical replay provenance recovery_receipt_path",
            ),
            "recovery_receipt_bytes_sha256": _bytes_sha256(
                recovered_manifest_store.recovery_receipt_bytes
            ),
            "authority_path": _normalized_paper_relative_path_text(
                recovered_manifest_store.authority_path,
                label="historical replay provenance recovered authority_path",
            ),
            "authority_bytes_sha256": _bytes_sha256(
                recovered_manifest_store.authority_bytes
            ),
            "carrier_compressed_path": _normalized_paper_relative_path_text(
                recovered_manifest_store.carrier_compressed_path,
                label="historical replay provenance carrier_compressed_path",
            ),
            "carrier_compressed_bytes_sha256": _bytes_sha256(
                recovered_manifest_store.carrier_compressed_bytes
            ),
        }
    else:
        provenance["policy_version"] = HISTORICAL_REPLAY_PROVENANCE_POLICY_VERSION
        provenance.update(
            {
                "historical_manifest_carrier_path": _normalized_paper_relative_path_text(
                    historical_manifest_carrier_path,
                    label="historical replay provenance historical_manifest_carrier_path",
                ),
                "historical_manifest_carrier_bytes_sha256": _required_sha256(
                    historical_manifest_carrier_bytes_sha256,
                    label=(
                        "historical replay provenance "
                        "historical_manifest_carrier_bytes_sha256"
                    ),
                ),
                "historical_manifest_authority_path": _normalized_paper_relative_path_text(
                    historical_manifest_authority_path,
                    label="historical replay provenance historical_manifest_authority_path",
                ),
                "historical_manifest_authority_bytes_sha256": _required_sha256(
                    historical_manifest_authority_bytes_sha256,
                    label=(
                        "historical replay provenance "
                        "historical_manifest_authority_bytes_sha256"
                    ),
                ),
            }
        )
    out[HISTORICAL_REPLAY_PROVENANCE_FIELD] = provenance
    if error := _current_entry_error(
        out,
        target=target,
        surface=surface,
        sidecar_prompt_version=str(prior.payload.get("prompt_version") or ""),
    ):
        raise StatementReceiptReissueError(
            "historical replay transport does not validate against the current receipt surface: "
            + error
        )
    return out


def _prior_reuse_error(
    prior: PriorSidecar,
    entry: Mapping[str, Any],
    *,
    target: CurrentReceiptTarget,
    surface: CurrentReceiptSurface,
) -> str:
    if not prior.present:
        return "reuse action names an absent prior sidecar"
    if prior.payload.get("schema") != 1:
        return "reuse action prior sidecar does not use statement-sidecar schema 1"
    if prior.payload.get("paper") not in {None, surface.paper}:
        return "reuse action prior sidecar names a different paper"
    if str(prior.payload.get("prompt_version") or "").strip() != review_dashboard.REQUIRED_LLM_STATEMENT_PROMPT_VERSION:
        return "reuse action prior sidecar has a stale statement-review prompt version"
    if (
        not str(prior.payload.get("validator") or "").strip()
        or not str(prior.payload.get("validator_type") or "").strip()
        or not str(prior.payload.get("validated_at") or "").strip()
    ):
        return "reuse action prior sidecar has no validator/type/timestamp metadata"
    if review_dashboard.is_non_evidence_scaffold_payload(dict(prior.payload)):
        return "reuse action prior sidecar is explicitly non-evidence"
    return _current_entry_error(
        entry,
        target=target,
        surface=surface,
        sidecar_prompt_version=str(prior.payload.get("prompt_version") or ""),
    )


def _string_digest_list(
    value: object, *, label: str, required: bool = False
) -> list[str]:
    if value is None:
        if required:
            raise StatementReceiptReissueError(f"{label} is required")
        return []
    if not isinstance(value, list):
        raise StatementReceiptReissueError(f"{label} must be a list")
    out = [_required_sha256(item, label=label) for item in value]
    if len(out) != len(set(out)):
        raise StatementReceiptReissueError(f"{label} has duplicate payload digests")
    return out


def _substantive_reason(value: object) -> str:
    text = str(value or "").strip()
    if len(text) < 40:
        raise StatementReceiptReissueError(
            "retire action must state a substantive source/Lean semantic anti-join reason"
        )
    return text


def _archive_payload(
    *,
    surface: CurrentReceiptSurface,
    prior: PriorSidecar,
    superseded: Sequence[str],
    retired: Sequence[str],
    historical_replay_transports: Sequence[Mapping[str, Any]],
    reviewer: str,
    validated_at: str,
) -> dict[str, Any] | None:
    if not prior.present:
        return None
    archive: dict[str, Any] = {
        "schema": REISSUE_SCHEMA,
        "artifact_kind": ARCHIVE_KIND,
        "policy_version": POLICY_VERSION,
        "paper": surface.paper,
        "current_inputs": surface.input_pins(),
        "archived_by": reviewer,
        "archived_at": validated_at,
        "prior_sidecar_sha256": prior.raw_sha256,
        "prior_sidecar_bytes_base64": base64.b64encode(prior.raw_bytes).decode("ascii"),
        "superseded_prior_entry_payload_sha256": sorted(set(superseded)),
        "retired_prior_entry_payload_sha256": sorted(set(retired)),
    }
    if historical_replay_transports:
        archive["historical_statement_manifest_replay_transports"] = sorted(
            [copy.deepcopy(dict(record)) for record in historical_replay_transports],
            key=lambda record: str(record["prior_entry_payload_sha256"]),
        )
    return archive


def materialize_statement_receipt_reissue(
    surface: CurrentReceiptSurface,
    prior: PriorSidecar,
    plan: Mapping[str, Any],
    *,
    historical_manifest_replay_receipt: Mapping[str, Any] | None = None,
    historical_manifest_replay_bytes: bytes | None = None,
    historical_manifest_replay_path: str | None = None,
    historical_manifest_carrier: Mapping[str, Any] | None = None,
    historical_manifest_carrier_bytes: bytes | None = None,
    historical_manifest_carrier_path: str | None = None,
    historical_manifest_authority: Mapping[str, Any] | None = None,
    historical_manifest_authority_bytes: bytes | None = None,
    historical_manifest_authority_path: str | None = None,
    historical_manifest_store_recovery_receipt: Mapping[str, Any] | None = None,
    historical_manifest_store_recovery_receipt_bytes: bytes | None = None,
    historical_manifest_store_recovery_receipt_path: str | None = None,
    historical_manifest_store_recovery_authority: Mapping[str, Any] | None = None,
    historical_manifest_store_recovery_authority_bytes: bytes | None = None,
    historical_manifest_store_recovery_authority_path: str | None = None,
    historical_manifest_store_recovery_carrier_compressed_bytes: bytes | None = None,
    historical_manifest_store_recovery_carrier_compressed_path: str | None = None,
    historical_manifest_current_source_record_audit: Mapping[str, Any] | None = None,
    historical_manifest_current_source_record_audit_bytes: bytes | None = None,
    historical_manifest_current_source_record_audit_path: str | None = None,
    historical_manifest_replay_archive_path: str | None = None,
    historical_manifest_replay_recipe_verifier: (
        HistoricalManifestReplayRecipeVerifier | None
    ) = None,
    historical_manifest_current_source_record_authority_verifier: (
        HistoricalManifestReplayCurrentClosureAuthorityVerifier | None
    ) = None,
) -> ReissueMaterialization:
    """Validate a reviewer plan and materialize a fresh ordinary sidecar.

    No plan field selects a target by source-map key, sidecar key, or Lean
    declaration name.  Every target is resolved through its full content hash.
    """

    if error := _current_surface_error(plan, surface):
        raise StatementReceiptReissueError(error)
    if error := _prior_plan_error(plan, prior):
        raise StatementReceiptReissueError(error)
    reviewer = _required_text(plan.get("reviewer"), label="plan reviewer")
    validator_type = _required_text(plan.get("validator_type"), label="plan validator_type")
    validated_at = _required_text(plan.get("validated_at"), label="plan validated_at")
    comment = _required_text(plan.get("comment"), label="plan comment")
    raw_actions = plan.get("actions")
    if not isinstance(raw_actions, list):
        raise StatementReceiptReissueError("plan actions must be a list")

    has_historical_replay_action = any(
        isinstance(raw_action, Mapping)
        and str(raw_action.get("action") or "").strip().lower()
        == HISTORICAL_REPLAY_ACTION
        for raw_action in raw_actions
    )
    historical_replay_context: (
        historical_manifest_replay.ValidatedHistoricalStatementManifestReplay | None
    ) = None
    historical_replay_receipt_sha256 = ""
    historical_replay_artifact_bytes_sha256 = ""
    historical_replay_inputs: HistoricalManifestReplayInputs | None = None
    if has_historical_replay_action:
        (
            historical_replay_context,
            historical_replay_inputs,
        ) = _validated_historical_manifest_replay(
            surface,
            prior,
            plan,
            receipt=historical_manifest_replay_receipt,
            receipt_bytes=historical_manifest_replay_bytes,
            artifact_path=historical_manifest_replay_path,
            historical_manifest_carrier=historical_manifest_carrier,
            historical_manifest_carrier_bytes=historical_manifest_carrier_bytes,
            historical_manifest_carrier_path=historical_manifest_carrier_path,
            historical_manifest_authority=historical_manifest_authority,
            historical_manifest_authority_bytes=historical_manifest_authority_bytes,
            historical_manifest_authority_path=historical_manifest_authority_path,
            historical_manifest_store_recovery_receipt=(
                historical_manifest_store_recovery_receipt
            ),
            historical_manifest_store_recovery_receipt_bytes=(
                historical_manifest_store_recovery_receipt_bytes
            ),
            historical_manifest_store_recovery_receipt_path=(
                historical_manifest_store_recovery_receipt_path
            ),
            historical_manifest_store_recovery_authority=(
                historical_manifest_store_recovery_authority
            ),
            historical_manifest_store_recovery_authority_bytes=(
                historical_manifest_store_recovery_authority_bytes
            ),
            historical_manifest_store_recovery_authority_path=(
                historical_manifest_store_recovery_authority_path
            ),
            historical_manifest_store_recovery_carrier_compressed_bytes=(
                historical_manifest_store_recovery_carrier_compressed_bytes
            ),
            historical_manifest_store_recovery_carrier_compressed_path=(
                historical_manifest_store_recovery_carrier_compressed_path
            ),
            current_source_record_audit=historical_manifest_current_source_record_audit,
            current_source_record_audit_bytes=(
                historical_manifest_current_source_record_audit_bytes
            ),
            current_source_record_audit_path=(
                historical_manifest_current_source_record_audit_path
            ),
            prior_sidecar_archive_path=historical_manifest_replay_archive_path,
            recipe_verifier=historical_manifest_replay_recipe_verifier,
            current_source_record_authority_verifier=(
                historical_manifest_current_source_record_authority_verifier
            ),
        )
        historical_replay_receipt_sha256 = _required_sha256(
            historical_replay_inputs.receipt.get(
                historical_manifest_replay.HISTORICAL_STATEMENT_MANIFEST_REPLAY_INTEGRITY_FIELD
            ),
            label="historical replay artifact integrity digest",
        )
        historical_replay_artifact_bytes_sha256 = _bytes_sha256(
            historical_replay_inputs.receipt_bytes
        )
    elif (
        HISTORICAL_REPLAY_PLAN_FIELD in plan
        or historical_manifest_replay_receipt is not None
        or historical_manifest_replay_bytes is not None
        or historical_manifest_replay_path is not None
        or historical_manifest_carrier is not None
        or historical_manifest_carrier_bytes is not None
        or historical_manifest_carrier_path is not None
        or historical_manifest_authority is not None
        or historical_manifest_authority_bytes is not None
        or historical_manifest_authority_path is not None
        or historical_manifest_store_recovery_receipt is not None
        or historical_manifest_store_recovery_receipt_bytes is not None
        or historical_manifest_store_recovery_receipt_path is not None
        or historical_manifest_store_recovery_authority is not None
        or historical_manifest_store_recovery_authority_bytes is not None
        or historical_manifest_store_recovery_authority_path is not None
        or historical_manifest_store_recovery_carrier_compressed_bytes is not None
        or historical_manifest_store_recovery_carrier_compressed_path is not None
        or historical_manifest_current_source_record_audit is not None
        or historical_manifest_current_source_record_audit_bytes is not None
        or historical_manifest_current_source_record_audit_path is not None
        or historical_manifest_replay_archive_path is not None
        or historical_manifest_replay_recipe_verifier is not None
        or historical_manifest_current_source_record_authority_verifier is not None
    ):
        raise StatementReceiptReissueError(
            "historical replay artifact is present but no historical_replay_reuse action uses it"
        )

    targets = {target.semantic_target_sha256: target for target in surface.targets}
    current_classes = {target.semantic_class_sha256 for target in surface.targets}
    output_items: dict[str, dict[str, Any]] = {}
    planned_targets: set[str] = set()
    consumed_prior_groups: set[str] = set()
    superseded: list[str] = []
    retired: list[str] = []
    reused: list[str] = []
    historical_replayed: list[str] = []
    historical_replay_transports: list[dict[str, Any]] = []
    fresh: list[str] = []

    def consume_prior_group(digest: str, *, action_label: str) -> list[dict[str, Any]]:
        if digest in consumed_prior_groups:
            raise StatementReceiptReissueError(
                f"{action_label} consumes a prior payload group more than once"
            )
        values = prior.groups.get(digest)
        if not values:
            raise StatementReceiptReissueError(
                f"{action_label} names an unknown prior entry payload digest"
            )
        consumed_prior_groups.add(digest)
        return values

    for position, raw_action in enumerate(raw_actions):
        label = f"action {position + 1}"
        if not isinstance(raw_action, Mapping):
            raise StatementReceiptReissueError(f"{label} is not an object")
        if error := _candidate_marker_error(raw_action, label=label):
            raise StatementReceiptReissueError(error)
        action = str(raw_action.get("action") or "").strip().lower()
        if action not in {"fresh", "reuse", "retire", HISTORICAL_REPLAY_ACTION}:
            raise StatementReceiptReissueError(f"{label} has invalid action")
        if action == "retire":
            if (
                "target" in raw_action
                or "body" in raw_action
                or "historical_manifest_replay_sha256" in raw_action
            ):
                raise StatementReceiptReissueError(
                    f"{label} retire action cannot carry a target, reviewer body, or replay receipt"
                )
            digest = _required_sha256(
                raw_action.get("prior_entry_payload_sha256"),
                label=f"{label} prior_entry_payload_sha256",
            )
            values = consume_prior_group(digest, action_label=label)
            _substantive_reason(raw_action.get("reason"))
            for value in values:
                semantic_class = _entry_semantic_class(value)
                if semantic_class and semantic_class in current_classes:
                    raise StatementReceiptReissueError(
                        f"{label} fails semantic anti-join: its prior Lean/translation "
                        "class remains in the current cache and needs explicit fresh supersession"
                    )
            retired.append(digest)
            continue

        target = _target_from_descriptor(raw_action.get("target"), targets)
        target_id = target.semantic_target_sha256
        if target_id in planned_targets:
            raise StatementReceiptReissueError(
                f"{label} duplicates a current semantic target action"
            )
        planned_targets.add(target_id)
        storage_key = _target_storage_key(target)
        if action == "fresh":
            if "historical_manifest_replay_sha256" in raw_action:
                raise StatementReceiptReissueError(
                    f"{label} fresh action cannot carry a historical replay receipt"
                )
            if error := _body_error(raw_action.get("body")):
                raise StatementReceiptReissueError(f"{label} {error}")
            prior_digests = _string_digest_list(
                raw_action.get("supersedes_prior_entry_payload_sha256"),
                label=f"{label} supersedes_prior_entry_payload_sha256",
            )
            for digest in prior_digests:
                values = consume_prior_group(digest, action_label=label)
                for value in values:
                    old_class = _entry_semantic_class(value)
                    if not old_class:
                        raise StatementReceiptReissueError(
                            f"{label} cannot supersede a prior payload without a valid "
                            "semantic identity; retire that SHA-pinned orphan explicitly"
                        )
                    if old_class != target.semantic_class_sha256:
                        raise StatementReceiptReissueError(
                            f"{label} tries to supersede a prior payload from a different "
                            "Lean/translation semantic class; retire it only after anti-join"
                        )
                superseded.append(digest)
            entry = _reviewer_body_without_transport(raw_action["body"])
            entry.update(
                {
                    "prompt_version": review_dashboard.REQUIRED_LLM_STATEMENT_PROMPT_VERSION,
                    "validator": reviewer,
                    "validator_type": validator_type,
                    "validated_at": validated_at,
                    "lean_statement_sha256": target.lean_statement_sha256,
                    **target.identity,
                }
            )
            if error := _current_entry_error(entry, target=target, surface=surface):
                raise StatementReceiptReissueError(f"{label} fresh body refused: {error}")
            output_items[storage_key] = entry
            fresh.append(target_id)
            continue

        if action == HISTORICAL_REPLAY_ACTION:
            if (
                "body" in raw_action
                or "supersedes_prior_entry_payload_sha256" in raw_action
            ):
                raise StatementReceiptReissueError(
                    f"{label} historical replay action cannot carry fresh reviewer content"
                )
            if historical_replay_context is None:
                raise StatementReceiptReissueError(
                    f"{label} has no statically validated historical replay artifact"
                )
            if historical_replay_inputs is None:  # Defensive invariant for the transport below.
                raise StatementReceiptReissueError(
                    f"{label} has no authenticated historical replay inputs"
                )
            action_receipt_sha = _required_sha256(
                raw_action.get("historical_manifest_replay_sha256"),
                label=f"{label} historical_manifest_replay_sha256",
            )
            if action_receipt_sha != historical_replay_receipt_sha256:
                raise StatementReceiptReissueError(
                    f"{label} replay receipt digest differs from the plan-pinned artifact"
                )
            digest = _required_sha256(
                raw_action.get("prior_entry_payload_sha256"),
                label=f"{label} prior_entry_payload_sha256",
            )
            values = consume_prior_group(digest, action_label=label)
            if len(values) != 1:
                raise StatementReceiptReissueError(
                    f"{label} cannot transport a duplicate prior payload group; issue one fresh receipt instead"
                )
            entry = copy.deepcopy(values[0])
            if "raw" in entry and len(entry) == 1:
                raise StatementReceiptReissueError(
                    f"{label} prior payload is not an evidence object"
                )
            binding = historical_manifest_replay.replay_binding_for_current_target(
                historical_replay_context,
                prior_entry_payload_sha256=digest,
                current_identity=target.identity,
            )
            if binding is None:
                raise StatementReceiptReissueError(
                    f"{label} has no exact historic-manifest binding for this prior/current content pair"
                )
            entry = _historical_manifest_replay_transport_entry(
                entry,
                binding=binding,
                target=target,
                surface=surface,
                prior=prior,
                replay_artifact_path=historical_replay_inputs.receipt_path,
                prior_payload_sha256=digest,
                replay_artifact_bytes_sha256=historical_replay_artifact_bytes_sha256,
                replay_receipt_sha256=historical_replay_receipt_sha256,
                historical_manifest_carrier_path=historical_replay_inputs.carrier_path,
                historical_manifest_carrier_bytes_sha256=(
                    None
                    if historical_replay_inputs.recovered_manifest_store is not None
                    else _bytes_sha256(historical_replay_inputs.carrier_bytes)
                ),
                historical_manifest_authority_path=historical_replay_inputs.authority_path,
                historical_manifest_authority_bytes_sha256=(
                    None
                    if historical_replay_inputs.recovered_manifest_store is not None
                    else _bytes_sha256(historical_replay_inputs.authority_bytes)
                ),
                current_source_record_audit_path=(
                    historical_replay_inputs.current_source_record_audit_path
                ),
                current_source_record_audit_bytes_sha256=_bytes_sha256(
                    historical_replay_inputs.current_source_record_audit_bytes
                ),
                current_lean_import_closure_sha256=(
                    historical_replay_inputs.current_lean_import_closure_sha256
                ),
                prior_sidecar_archive_path=(
                    historical_replay_inputs.prior_sidecar_archive_path
                ),
                recovered_manifest_store=(
                    historical_replay_inputs.recovered_manifest_store
                ),
            )
            output_items[storage_key] = entry
            historical_replayed.append(target_id)
            provenance = entry.get(HISTORICAL_REPLAY_PROVENANCE_FIELD)
            assert isinstance(provenance, dict)
            historical_replay_transports.append(copy.deepcopy(provenance))
            continue

        # Reuse: only an exact current receipt can remain evidence.  It is
        # copied without reauthoring its judgment body or generated pins.
        if (
            "body" in raw_action
            or "supersedes_prior_entry_payload_sha256" in raw_action
            or "historical_manifest_replay_sha256" in raw_action
        ):
            raise StatementReceiptReissueError(
                f"{label} reuse action cannot carry fresh reviewer content or replay evidence"
            )
        digest = _required_sha256(
            raw_action.get("prior_entry_payload_sha256"),
            label=f"{label} prior_entry_payload_sha256",
        )
        values = consume_prior_group(digest, action_label=label)
        if len(values) != 1:
            raise StatementReceiptReissueError(
                f"{label} cannot reuse a duplicate prior payload group; issue one fresh receipt instead"
            )
        entry = copy.deepcopy(values[0])
        if "raw" in entry and len(entry) == 1:
            raise StatementReceiptReissueError(f"{label} prior payload is not an evidence object")
        if _entry_semantic_identity(entry) != target.identity:
            raise StatementReceiptReissueError(
                f"{label} reuse target differs from the prior receipt semantic identity"
            )
        if error := _prior_reuse_error(prior, entry, target=target, surface=surface):
            raise StatementReceiptReissueError(f"{label} reuse refused: {error}")
        output_items[storage_key] = entry
        reused.append(target_id)

    expected_targets = set(targets)
    missing_targets = sorted(expected_targets - planned_targets)
    if missing_targets:
        raise StatementReceiptReissueError(
            "plan does not classify every current semantic target: "
            + ", ".join(missing_targets)
        )
    unclassified_prior = sorted(set(prior.groups) - consumed_prior_groups)
    if unclassified_prior:
        raise StatementReceiptReissueError(
            "plan does not classify every prior entry payload group: "
            + ", ".join(unclassified_prior)
        )

    sidecar = {
        "schema": 1,
        "paper": surface.paper,
        "prompt_version": review_dashboard.REQUIRED_LLM_STATEMENT_PROMPT_VERSION,
        "validator": reviewer,
        "validator_type": validator_type,
        "validated_at": validated_at,
        "semantic_contract": review_dashboard.REQUIRED_LLM_STATEMENT_SEMANTIC_CONTRACT_VERSION,
        "comment": comment,
        "items": dict(sorted(output_items.items())),
    }
    if surface.source_record_audit_sha256:
        sidecar["source_record_audit_sha256"] = surface.source_record_audit_sha256
    archive = _archive_payload(
        surface=surface,
        prior=prior,
        superseded=superseded,
        retired=retired,
        historical_replay_transports=historical_replay_transports,
        reviewer=reviewer,
        validated_at=validated_at,
    )
    return ReissueMaterialization(
        sidecar=sidecar,
        archive=archive,
        report={
            "paper": surface.paper,
            "current_target_count": len(targets),
            "fresh_target_count": len(fresh),
            "reused_target_count": len(reused),
            "historical_replay_reused_target_count": len(historical_replayed),
            "historical_replay_receipt_sha256": (
                historical_replay_receipt_sha256 or None
            ),
            "historical_replay_artifact_bytes_sha256": (
                historical_replay_artifact_bytes_sha256 or None
            ),
            "retired_prior_payload_group_count": len(retired),
            "superseded_prior_payload_group_count": len(superseded),
            "prior_payload_group_count": len(prior.groups),
            "current_surface_sha256": surface.current_surface_sha256,
            "dry_run": True,
        },
    )


def _archived_prior_for_already_applied_check(
    archive_path: Path | None,
) -> tuple[PriorSidecar, bytes] | None:
    """Recover a prior sidecar only from a readable exact-byte archive.

    This helper deliberately does not treat a parsed archive as evidence by
    itself.  The caller also compares its raw bytes to the archive that this
    exact plan would have produced.  That prevents a later plan run from using
    an arbitrary old sidecar merely because its payload happens to parse.
    """

    if archive_path is None or not archive_path.is_file():
        return None
    try:
        archive_raw = archive_path.read_bytes()
        archive = _read_json_object(archive_raw, label="receipt-reissue archive")
        encoded_prior = archive.get("prior_sidecar_bytes_base64")
        if not isinstance(encoded_prior, str):
            return None
        prior_raw = base64.b64decode(encoded_prior, validate=True)
        if _bytes_sha256(prior_raw) != _sha256(archive.get("prior_sidecar_sha256")):
            return None
        return (
            _prior_sidecar_from_raw(
                prior_raw, label="receipt-reissue archive prior sidecar"
            ),
            archive_raw,
        )
    except (OSError, UnicodeDecodeError, ValueError, StatementReceiptReissueError):
        return None


def already_applied_statement_receipt_reissue(
    surface: CurrentReceiptSurface,
    current: PriorSidecar,
    plan: Mapping[str, Any],
    *,
    archive_path: Path | None = None,
    historical_manifest_replay_receipt: Mapping[str, Any] | None = None,
    historical_manifest_replay_bytes: bytes | None = None,
    historical_manifest_replay_path: str | None = None,
    historical_manifest_carrier: Mapping[str, Any] | None = None,
    historical_manifest_carrier_bytes: bytes | None = None,
    historical_manifest_carrier_path: str | None = None,
    historical_manifest_authority: Mapping[str, Any] | None = None,
    historical_manifest_authority_bytes: bytes | None = None,
    historical_manifest_authority_path: str | None = None,
    historical_manifest_store_recovery_receipt: Mapping[str, Any] | None = None,
    historical_manifest_store_recovery_receipt_bytes: bytes | None = None,
    historical_manifest_store_recovery_receipt_path: str | None = None,
    historical_manifest_store_recovery_authority: Mapping[str, Any] | None = None,
    historical_manifest_store_recovery_authority_bytes: bytes | None = None,
    historical_manifest_store_recovery_authority_path: str | None = None,
    historical_manifest_store_recovery_carrier_compressed_bytes: bytes | None = None,
    historical_manifest_store_recovery_carrier_compressed_path: str | None = None,
    historical_manifest_current_source_record_audit: Mapping[str, Any] | None = None,
    historical_manifest_current_source_record_audit_bytes: bytes | None = None,
    historical_manifest_current_source_record_audit_path: str | None = None,
    historical_manifest_replay_archive_path: str | None = None,
    historical_manifest_replay_recipe_verifier: (
        HistoricalManifestReplayRecipeVerifier | None
    ) = None,
    historical_manifest_current_source_record_authority_verifier: (
        HistoricalManifestReplayCurrentClosureAuthorityVerifier | None
    ) = None,
) -> ReissueMaterialization | None:
    """Prove an already-applied plan without relaxing ordinary stale-plan pins.

    A completed plan cannot normally be materialized again: its prior-sidecar
    byte pin intentionally differs from the replacement sidecar.  It is a
    no-op only when the current sidecar is *byte-for-byte* the deterministic
    output of the plan.  When the plan replaced a prior sidecar, that output is
    reconstructed solely from the exact archive written by the original run;
    the archive must itself be byte-for-byte the one this plan would produce.

    This is intentionally a proof of completion, not a fallback reuse path.
    Missing, altered, or merely semantically similar output/archive data
    returns ``None`` so the ordinary materializer keeps refusing the stale
    plan.
    """

    descriptor = plan.get("prior_sidecar")
    if not isinstance(descriptor, Mapping):
        return None
    prior_present = descriptor.get("present")
    if prior_present is True:
        recovered = _archived_prior_for_already_applied_check(archive_path)
        if recovered is None:
            return None
        prior, archive_raw = recovered
    elif prior_present is False:
        prior = PriorSidecar(False, b"", "", {}, {})
        archive_raw = None
    else:
        return None

    try:
        materialized = materialize_statement_receipt_reissue(
            surface,
            prior,
            plan,
            historical_manifest_replay_receipt=historical_manifest_replay_receipt,
            historical_manifest_replay_bytes=historical_manifest_replay_bytes,
            historical_manifest_replay_path=historical_manifest_replay_path,
            historical_manifest_carrier=historical_manifest_carrier,
            historical_manifest_carrier_bytes=historical_manifest_carrier_bytes,
            historical_manifest_carrier_path=historical_manifest_carrier_path,
            historical_manifest_authority=historical_manifest_authority,
            historical_manifest_authority_bytes=historical_manifest_authority_bytes,
            historical_manifest_authority_path=historical_manifest_authority_path,
            historical_manifest_store_recovery_receipt=(
                historical_manifest_store_recovery_receipt
            ),
            historical_manifest_store_recovery_receipt_bytes=(
                historical_manifest_store_recovery_receipt_bytes
            ),
            historical_manifest_store_recovery_receipt_path=(
                historical_manifest_store_recovery_receipt_path
            ),
            historical_manifest_store_recovery_authority=(
                historical_manifest_store_recovery_authority
            ),
            historical_manifest_store_recovery_authority_bytes=(
                historical_manifest_store_recovery_authority_bytes
            ),
            historical_manifest_store_recovery_authority_path=(
                historical_manifest_store_recovery_authority_path
            ),
            historical_manifest_store_recovery_carrier_compressed_bytes=(
                historical_manifest_store_recovery_carrier_compressed_bytes
            ),
            historical_manifest_store_recovery_carrier_compressed_path=(
                historical_manifest_store_recovery_carrier_compressed_path
            ),
            historical_manifest_current_source_record_audit=(
                historical_manifest_current_source_record_audit
            ),
            historical_manifest_current_source_record_audit_bytes=(
                historical_manifest_current_source_record_audit_bytes
            ),
            historical_manifest_current_source_record_audit_path=(
                historical_manifest_current_source_record_audit_path
            ),
            historical_manifest_replay_archive_path=(
                historical_manifest_replay_archive_path
            ),
            historical_manifest_replay_recipe_verifier=(
                historical_manifest_replay_recipe_verifier
            ),
            historical_manifest_current_source_record_authority_verifier=(
                historical_manifest_current_source_record_authority_verifier
            ),
        )
    except StatementReceiptReissueError:
        return None
    if current.raw_bytes != _json_bytes(materialized.sidecar):
        return None
    if prior.present:
        if materialized.archive is None:
            return None
        if archive_raw != _json_bytes(materialized.archive):
            return None

    report = dict(materialized.report)
    report["already_applied"] = True
    report["dry_run"] = True
    return ReissueMaterialization(
        sidecar=materialized.sidecar,
        archive=materialized.archive,
        report=report,
    )


def _paper_relative_path(path: Path, paper_dir: Path, *, label: str) -> Path:
    raw = str(path)
    pure = PurePosixPath(raw)
    if pure.is_absolute() or not raw or any(part in {"", ".", ".."} for part in pure.parts):
        raise StatementReceiptReissueError(f"{label} must be a normalized paper-relative path")
    resolved = (paper_dir / Path(*pure.parts)).resolve()
    try:
        relative = resolved.relative_to(paper_dir.resolve()).as_posix()
    except ValueError as exc:
        raise StatementReceiptReissueError(
            f"{label} escapes the paper directory"
        ) from exc
    if relative != raw:
        raise StatementReceiptReissueError(f"{label} is not canonical")
    return resolved


def _historical_manifest_replay_cli_recipe_verifier(
    *,
    root: Path,
    paper_dir: Path,
    current_lean_import_closure: Mapping[str, object],
    current_lean_import_closure_bytes: bytes,
) -> HistoricalManifestReplayRecipeVerifier:
    """Construct the production no-Lean recipe verifier for one paper.

    This verifier deliberately has no Lean import module or declaration route:
    materialization only validates Git blobs and exact current file pins.  The
    canonical PaperInterface path is derived from the selected paper directory,
    which keeps the verifier bound to the same source file that the current
    receipt surface reviewed.
    """

    try:
        interface_path = (paper_dir / "PaperInterface.lean").resolve()
        relative_interface = interface_path.relative_to(root.resolve()).as_posix()
    except ValueError as exc:
        raise StatementReceiptReissueError(
            "canonical PaperInterface path escapes this repository root"
        ) from exc
    try:
        return historical_manifest_runner.make_historical_statement_manifest_recipe_verifier(
            root=root,
            paper_interface_path=relative_interface,
            current_lean_import_closure=current_lean_import_closure,
            current_lean_import_closure_bytes=current_lean_import_closure_bytes,
        )
    except historical_manifest_runner.HistoricalStatementManifestRunnerError as exc:
        raise StatementReceiptReissueError(
            "could not configure historical replay recipe verification: " + str(exc)
        ) from exc


def _atomic_write(path: Path, contents: bytes) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    temporary: Path | None = None
    try:
        with tempfile.NamedTemporaryFile(
            dir=path.parent,
            prefix=f".{path.name}.",
            delete=False,
        ) as handle:
            handle.write(contents)
            temporary = Path(handle.name)
        os.replace(temporary, path)
        temporary = None
    finally:
        if temporary is not None and temporary.exists():
            temporary.unlink()


def _json_bytes(value: object) -> bytes:
    return (json.dumps(value, ensure_ascii=False, indent=2, sort_keys=True) + "\n").encode(
        "utf-8"
    )


def _load_plan(path: Path) -> dict[str, Any]:
    return _read_json_object(path.read_bytes(), label="reissue plan")


def _same_surface(
    left: CurrentReceiptSurface, right: CurrentReceiptSurface
) -> bool:
    """Compare the complete content-pinned surface, never row navigation."""

    return (
        left.paper == right.paper
        and left.input_pins() == right.input_pins()
        and left.source_map_semantic_sha256 == right.source_map_semantic_sha256
        and [target.descriptor() for target in left.targets]
        == [target.descriptor() for target in right.targets]
    )


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", type=Path, default=ROOT)
    parser.add_argument("--paper", required=True, help="paper folder under papers/")
    mode = parser.add_mutually_exclusive_group(required=True)
    mode.add_argument(
        "--emit-template",
        type=Path,
        help="write a non-evidence content-pinned reviewer template inside the paper",
    )
    mode.add_argument(
        "--emit-action-scaffold",
        type=Path,
        help=(
            "write a non-evidence content-pinned reuse/fresh/retire candidate "
            "scaffold inside the paper"
        ),
    )
    mode.add_argument(
        "--plan",
        type=Path,
        help="completed reviewer plan to materialize into the ordinary statement sidecar",
    )
    parser.add_argument(
        "--out",
        type=Path,
        help="ordinary statement sidecar output (required with --plan)",
    )
    parser.add_argument(
        "--archive",
        type=Path,
        help="exact-byte prior-sidecar archive (required with --plan when prior sidecar exists)",
    )
    parser.add_argument(
        "--historical-manifest-replay",
        type=Path,
        help=(
            "plan-pinned historical serializer replay artifact for one or more "
            "historical_replay_reuse actions"
        ),
    )
    parser.add_argument(
        "--historical-manifest-carrier",
        type=Path,
        help=(
            "byte-pinned authenticated historic manifest carrier required by "
            "--historical-manifest-replay"
        ),
    )
    parser.add_argument(
        "--historical-manifest-authority",
        type=Path,
        help=(
            "byte-pinned authenticated historic manifest authority required by "
            "--historical-manifest-replay"
        ),
    )
    parser.add_argument(
        "--historical-manifest-store-recovery-receipt",
        type=Path,
        help=(
            "byte-pinned recovered manifest-store receipt JSON; use with the "
            "recovered authority and deterministic gzip carrier instead of "
            "--historical-manifest-carrier/--historical-manifest-authority"
        ),
    )
    parser.add_argument(
        "--historical-manifest-store-recovery-authority",
        type=Path,
        help=(
            "byte-pinned recovered manifest-store authority JSON required by "
            "--historical-manifest-store-recovery-receipt"
        ),
    )
    parser.add_argument(
        "--historical-manifest-store-recovery-carrier",
        type=Path,
        help=(
            "byte-pinned deterministic gzip recovered manifest-store carrier "
            "required by --historical-manifest-store-recovery-receipt"
        ),
    )
    parser.add_argument(
        "--historical-source-record-audit",
        type=Path,
        help=(
            "byte-pinned completed current source-record audit whose Lean import "
            "closure is required by --historical-manifest-replay"
        ),
    )
    parser.add_argument(
        "--write",
        action="store_true",
        help="write --out and --archive after validation; default is dry run",
    )
    parser.add_argument(
        "--allow-all-reuse-rewrite",
        action="store_true",
        help=(
            "allow an otherwise no-op all-reuse plan to rewrite sidecar storage "
            "and create an archive; only for an explicit storage migration"
        ),
    )
    return parser.parse_args()


def main() -> int:
    args = parse_args()
    root = args.root.resolve()
    try:
        # ``review_dashboard`` owns the manifest/build-input authority. Do not
        # pretend a copied directory has the same Lean environment merely
        # because its file layout resembles this repository.
        if root != ROOT.resolve():
            raise StatementReceiptReissueError(
                "--root must be this repository root; copied roots need their own audit authority"
            )
        paper_dir = root / "papers" / args.paper
        if not paper_dir.is_dir():
            raise StatementReceiptReissueError("paper directory is unavailable")
        surface = current_statement_receipt_surface(paper_dir)
        sidecar_path = paper_dir / "audit" / "statement_match_llm.json"
        prior = load_prior_sidecar(sidecar_path)
        if args.emit_template is not None:
            if (
                args.out is not None
                or args.archive is not None
                or args.historical_manifest_replay is not None
                or args.historical_manifest_carrier is not None
                or args.historical_manifest_authority is not None
                or args.historical_manifest_store_recovery_receipt is not None
                or args.historical_manifest_store_recovery_authority is not None
                or args.historical_manifest_store_recovery_carrier is not None
                or args.historical_source_record_audit is not None
                or args.write
                or args.allow_all_reuse_rewrite
            ):
                raise StatementReceiptReissueError(
                    "--emit-template cannot be combined with plan materialization options"
                )
            template_path = _paper_relative_path(
                args.emit_template, paper_dir, label="--emit-template"
            )
            _atomic_write(template_path, _json_bytes(statement_receipt_reissue_template(surface, prior)))
            print(
                f"{args.paper}: wrote non-evidence receipt-reissue template to {template_path} "
                f"({len(surface.targets)} current content targets)"
            )
            return 0
        if args.emit_action_scaffold is not None:
            if (
                args.out is not None
                or args.archive is not None
                or args.historical_manifest_replay is not None
                or args.historical_manifest_carrier is not None
                or args.historical_manifest_authority is not None
                or args.historical_manifest_store_recovery_receipt is not None
                or args.historical_manifest_store_recovery_authority is not None
                or args.historical_manifest_store_recovery_carrier is not None
                or args.historical_source_record_audit is not None
                or args.write
                or args.allow_all_reuse_rewrite
            ):
                raise StatementReceiptReissueError(
                    "--emit-action-scaffold cannot be combined with plan materialization options"
                )
            scaffold_path = _paper_relative_path(
                args.emit_action_scaffold,
                paper_dir,
                label="--emit-action-scaffold",
            )
            scaffold = statement_receipt_reissue_action_scaffold(surface, prior)
            _atomic_write(scaffold_path, _json_bytes(scaffold))
            print(
                f"{args.paper}: wrote non-evidence receipt action scaffold to "
                f"{scaffold_path} ({len(scaffold['candidate_actions'])} candidates, "
                f"{len(scaffold['unresolved_semantic_classes'])} unresolved classes)"
            )
            return 0
        if args.plan is None or args.out is None:
            raise StatementReceiptReissueError("--plan requires --out")
        plan_path = _paper_relative_path(args.plan, paper_dir, label="--plan")
        output_path = _paper_relative_path(args.out, paper_dir, label="--out")
        if output_path != sidecar_path.resolve():
            raise StatementReceiptReissueError(
                "--out must be the canonical audit/statement_match_llm.json sidecar"
            )
        archive_path: Path | None = None
        if args.archive is not None:
            archive_path = _paper_relative_path(args.archive, paper_dir, label="--archive")
            if archive_path in {output_path, plan_path}:
                raise StatementReceiptReissueError("--archive must differ from --out and --plan")
        plan = _load_plan(plan_path)
        historical_replay_path: Path | None = None
        historical_replay_raw: bytes | None = None
        historical_replay_receipt: dict[str, Any] | None = None
        historical_replay_relative_path: str | None = None
        historical_manifest_carrier_path: Path | None = None
        historical_manifest_carrier_raw: bytes | None = None
        historical_manifest_carrier: dict[str, Any] | None = None
        historical_manifest_carrier_relative_path: str | None = None
        historical_manifest_authority_path: Path | None = None
        historical_manifest_authority_raw: bytes | None = None
        historical_manifest_authority: dict[str, Any] | None = None
        historical_manifest_authority_relative_path: str | None = None
        historical_manifest_store_recovery_receipt_path: Path | None = None
        historical_manifest_store_recovery_receipt_raw: bytes | None = None
        historical_manifest_store_recovery_receipt: dict[str, Any] | None = None
        historical_manifest_store_recovery_receipt_relative_path: str | None = None
        historical_manifest_store_recovery_authority_path: Path | None = None
        historical_manifest_store_recovery_authority_raw: bytes | None = None
        historical_manifest_store_recovery_authority: dict[str, Any] | None = None
        historical_manifest_store_recovery_authority_relative_path: str | None = None
        historical_manifest_store_recovery_carrier_path: Path | None = None
        historical_manifest_store_recovery_carrier_raw: bytes | None = None
        historical_manifest_store_recovery_carrier_relative_path: str | None = None
        historical_source_record_audit_path: Path | None = None
        historical_source_record_audit_raw: bytes | None = None
        historical_source_record_audit: dict[str, Any] | None = None
        historical_source_record_audit_relative_path: str | None = None
        historical_replay_recipe_verifier: (
            HistoricalManifestReplayRecipeVerifier | None
        ) = None
        legacy_store_args = (
            args.historical_manifest_carrier,
            args.historical_manifest_authority,
        )
        recovered_store_args = (
            args.historical_manifest_store_recovery_receipt,
            args.historical_manifest_store_recovery_authority,
            args.historical_manifest_store_recovery_carrier,
        )
        if args.historical_manifest_replay is None and (
            any(value is not None for value in legacy_store_args)
            or any(value is not None for value in recovered_store_args)
            or args.historical_source_record_audit is not None
        ):
            raise StatementReceiptReissueError(
                "historical manifest-store and source-record inputs require "
                "--historical-manifest-replay"
            )
        if args.historical_manifest_replay is not None:
            has_legacy_store = any(value is not None for value in legacy_store_args)
            has_recovered_store = any(
                value is not None for value in recovered_store_args
            )
            if has_legacy_store and has_recovered_store:
                raise StatementReceiptReissueError(
                    "--historical-manifest-carrier/--historical-manifest-authority "
                    "cannot be combined with recovered manifest-store inputs"
                )
            if args.historical_source_record_audit is None or (
                not has_legacy_store and not has_recovered_store
            ):
                raise StatementReceiptReissueError(
                    "--historical-manifest-replay requires --historical-source-record-audit "
                    "and either the uncompressed carrier/authority pair or the recovered "
                    "receipt/authority/gzip-carrier bundle"
                )
            if has_legacy_store and any(value is None for value in legacy_store_args):
                raise StatementReceiptReissueError(
                    "--historical-manifest-replay requires both --historical-manifest-carrier "
                    "and --historical-manifest-authority"
                )
            if has_recovered_store and any(
                value is None for value in recovered_store_args
            ):
                raise StatementReceiptReissueError(
                    "recovered manifest-store replay requires receipt, authority, and "
                    "deterministic gzip carrier inputs"
                )
            historical_replay_path = _paper_relative_path(
                args.historical_manifest_replay,
                paper_dir,
                label="--historical-manifest-replay",
            )
            historical_source_record_audit_path = _paper_relative_path(
                args.historical_source_record_audit,
                paper_dir,
                label="--historical-source-record-audit",
            )
            historical_paths: set[Path] = {
                historical_replay_path,
                historical_source_record_audit_path,
            }
            if has_legacy_store:
                assert args.historical_manifest_carrier is not None
                assert args.historical_manifest_authority is not None
                historical_manifest_carrier_path = _paper_relative_path(
                    args.historical_manifest_carrier,
                    paper_dir,
                    label="--historical-manifest-carrier",
                )
                historical_manifest_authority_path = _paper_relative_path(
                    args.historical_manifest_authority,
                    paper_dir,
                    label="--historical-manifest-authority",
                )
                historical_paths.update(
                    {
                        historical_manifest_carrier_path,
                        historical_manifest_authority_path,
                    }
                )
            else:
                assert args.historical_manifest_store_recovery_receipt is not None
                assert args.historical_manifest_store_recovery_authority is not None
                assert args.historical_manifest_store_recovery_carrier is not None
                historical_manifest_store_recovery_receipt_path = _paper_relative_path(
                    args.historical_manifest_store_recovery_receipt,
                    paper_dir,
                    label="--historical-manifest-store-recovery-receipt",
                )
                historical_manifest_store_recovery_authority_path = _paper_relative_path(
                    args.historical_manifest_store_recovery_authority,
                    paper_dir,
                    label="--historical-manifest-store-recovery-authority",
                )
                historical_manifest_store_recovery_carrier_path = _paper_relative_path(
                    args.historical_manifest_store_recovery_carrier,
                    paper_dir,
                    label="--historical-manifest-store-recovery-carrier",
                )
                historical_paths.update(
                    {
                        historical_manifest_store_recovery_receipt_path,
                        historical_manifest_store_recovery_authority_path,
                        historical_manifest_store_recovery_carrier_path,
                    }
                )
            expected_historical_path_count = 4 if has_legacy_store else 5
            if len(historical_paths) != expected_historical_path_count or historical_paths & {
                output_path,
                plan_path,
                archive_path,
            }:
                raise StatementReceiptReissueError(
                    "historical replay inputs must be distinct from each other and from "
                    "--out, --plan, and --archive"
                )
            if not all(path.is_file() for path in historical_paths):
                raise StatementReceiptReissueError(
                    "historical replay inputs must be regular files"
                )
            historical_replay_raw = historical_replay_path.read_bytes()
            historical_replay_receipt = _read_json_object(
                historical_replay_raw,
                label="historical replay artifact",
            )
            historical_replay_relative_path = str(args.historical_manifest_replay)
            if has_legacy_store:
                assert historical_manifest_carrier_path is not None
                assert historical_manifest_authority_path is not None
                historical_manifest_carrier_raw = historical_manifest_carrier_path.read_bytes()
                historical_manifest_carrier = _read_json_object(
                    historical_manifest_carrier_raw,
                    label="historical manifest carrier",
                )
                historical_manifest_carrier_relative_path = str(
                    args.historical_manifest_carrier
                )
                historical_manifest_authority_raw = (
                    historical_manifest_authority_path.read_bytes()
                )
                historical_manifest_authority = _read_json_object(
                    historical_manifest_authority_raw,
                    label="historical manifest authority",
                )
                historical_manifest_authority_relative_path = str(
                    args.historical_manifest_authority
                )
            else:
                assert historical_manifest_store_recovery_receipt_path is not None
                assert historical_manifest_store_recovery_authority_path is not None
                assert historical_manifest_store_recovery_carrier_path is not None
                historical_manifest_store_recovery_receipt_raw = (
                    historical_manifest_store_recovery_receipt_path.read_bytes()
                )
                historical_manifest_store_recovery_receipt = _read_json_object(
                    historical_manifest_store_recovery_receipt_raw,
                    label="historical manifest-store recovery receipt",
                )
                historical_manifest_store_recovery_receipt_relative_path = str(
                    args.historical_manifest_store_recovery_receipt
                )
                historical_manifest_store_recovery_authority_raw = (
                    historical_manifest_store_recovery_authority_path.read_bytes()
                )
                historical_manifest_store_recovery_authority = _read_json_object(
                    historical_manifest_store_recovery_authority_raw,
                    label="historical manifest-store recovery authority",
                )
                historical_manifest_store_recovery_authority_relative_path = str(
                    args.historical_manifest_store_recovery_authority
                )
                historical_manifest_store_recovery_carrier_raw = (
                    historical_manifest_store_recovery_carrier_path.read_bytes()
                )
                historical_manifest_store_recovery_carrier_relative_path = str(
                    args.historical_manifest_store_recovery_carrier
                )
            historical_source_record_audit_raw = historical_source_record_audit_path.read_bytes()
            historical_source_record_audit = _read_json_object(
                historical_source_record_audit_raw,
                label="historical replay current source-record audit",
            )
            historical_source_record_audit_relative_path = str(
                args.historical_source_record_audit
            )
            replay_inputs = _historical_manifest_replay_plan_descriptor(
                plan,
                surface=surface,
                receipt=historical_replay_receipt,
                receipt_bytes=historical_replay_raw,
                artifact_path=historical_replay_relative_path,
                historical_manifest_carrier=historical_manifest_carrier,
                historical_manifest_carrier_bytes=historical_manifest_carrier_raw,
                historical_manifest_carrier_path=(
                    historical_manifest_carrier_relative_path
                ),
                historical_manifest_authority=historical_manifest_authority,
                historical_manifest_authority_bytes=historical_manifest_authority_raw,
                historical_manifest_authority_path=(
                    historical_manifest_authority_relative_path
                ),
                current_source_record_audit=historical_source_record_audit,
                current_source_record_audit_bytes=historical_source_record_audit_raw,
                current_source_record_audit_path=(
                    historical_source_record_audit_relative_path
                ),
                prior_sidecar_archive_path=(
                    str(args.archive) if args.archive is not None else None
                ),
                historical_manifest_store_recovery_receipt=(
                    historical_manifest_store_recovery_receipt
                ),
                historical_manifest_store_recovery_receipt_bytes=(
                    historical_manifest_store_recovery_receipt_raw
                ),
                historical_manifest_store_recovery_receipt_path=(
                    historical_manifest_store_recovery_receipt_relative_path
                ),
                historical_manifest_store_recovery_authority=(
                    historical_manifest_store_recovery_authority
                ),
                historical_manifest_store_recovery_authority_bytes=(
                    historical_manifest_store_recovery_authority_raw
                ),
                historical_manifest_store_recovery_authority_path=(
                    historical_manifest_store_recovery_authority_relative_path
                ),
                historical_manifest_store_recovery_carrier_compressed_bytes=(
                    historical_manifest_store_recovery_carrier_raw
                ),
                historical_manifest_store_recovery_carrier_compressed_path=(
                    historical_manifest_store_recovery_carrier_relative_path
                ),
            )
            historical_replay_recipe_verifier = (
                _historical_manifest_replay_cli_recipe_verifier(
                    root=root,
                    paper_dir=paper_dir,
                    current_lean_import_closure=(
                        replay_inputs.current_lean_import_closure
                    ),
                    current_lean_import_closure_bytes=(
                        replay_inputs.current_lean_import_closure_bytes
                    ),
                )
            )
        historical_replay_archive_relative_path = (
            str(args.archive)
            if args.historical_manifest_replay is not None and args.archive is not None
            else None
        )
        # The common initial materialization case has exactly the plan's prior
        # sidecar in place, so it cannot already be applied.  Skipping the
        # reconstruction in that case avoids validating the same historic
        # bridge twice.  Only a mismatched prior state can be a post-write
        # sidecar that needs archive-based completion recovery.
        already_applied: ReissueMaterialization | None = None
        if _prior_plan_error(plan, prior):
            already_applied = already_applied_statement_receipt_reissue(
                surface,
                prior,
                plan,
                archive_path=archive_path,
                historical_manifest_replay_receipt=historical_replay_receipt,
                historical_manifest_replay_bytes=historical_replay_raw,
                historical_manifest_replay_path=historical_replay_relative_path,
                historical_manifest_carrier=historical_manifest_carrier,
                historical_manifest_carrier_bytes=historical_manifest_carrier_raw,
                historical_manifest_carrier_path=historical_manifest_carrier_relative_path,
                historical_manifest_authority=historical_manifest_authority,
                historical_manifest_authority_bytes=historical_manifest_authority_raw,
                historical_manifest_authority_path=(
                    historical_manifest_authority_relative_path
                ),
                historical_manifest_store_recovery_receipt=(
                    historical_manifest_store_recovery_receipt
                ),
                historical_manifest_store_recovery_receipt_bytes=(
                    historical_manifest_store_recovery_receipt_raw
                ),
                historical_manifest_store_recovery_receipt_path=(
                    historical_manifest_store_recovery_receipt_relative_path
                ),
                historical_manifest_store_recovery_authority=(
                    historical_manifest_store_recovery_authority
                ),
                historical_manifest_store_recovery_authority_bytes=(
                    historical_manifest_store_recovery_authority_raw
                ),
                historical_manifest_store_recovery_authority_path=(
                    historical_manifest_store_recovery_authority_relative_path
                ),
                historical_manifest_store_recovery_carrier_compressed_bytes=(
                    historical_manifest_store_recovery_carrier_raw
                ),
                historical_manifest_store_recovery_carrier_compressed_path=(
                    historical_manifest_store_recovery_carrier_relative_path
                ),
                historical_manifest_current_source_record_audit=(
                    historical_source_record_audit
                ),
                historical_manifest_current_source_record_audit_bytes=(
                    historical_source_record_audit_raw
                ),
                historical_manifest_current_source_record_audit_path=(
                    historical_source_record_audit_relative_path
                ),
                historical_manifest_replay_archive_path=(
                    historical_replay_archive_relative_path
                ),
                historical_manifest_replay_recipe_verifier=(
                    historical_replay_recipe_verifier
                ),
            )
        if already_applied is not None:
            report = already_applied.report
            print(
                f"{args.paper}: receipt reissue already applied; current sidecar and "
                "applicable archive exactly match the deterministic plan output "
                f"({report['fresh_target_count']} fresh, "
                f"{report['reused_target_count']} reused, "
                f"{report['historical_replay_reused_target_count']} historically transported)"
            )
            return 0
        materialized = materialize_statement_receipt_reissue(
            surface,
            prior,
            plan,
            historical_manifest_replay_receipt=historical_replay_receipt,
            historical_manifest_replay_bytes=historical_replay_raw,
            historical_manifest_replay_path=historical_replay_relative_path,
            historical_manifest_carrier=historical_manifest_carrier,
            historical_manifest_carrier_bytes=historical_manifest_carrier_raw,
            historical_manifest_carrier_path=historical_manifest_carrier_relative_path,
            historical_manifest_authority=historical_manifest_authority,
            historical_manifest_authority_bytes=historical_manifest_authority_raw,
            historical_manifest_authority_path=(
                historical_manifest_authority_relative_path
            ),
            historical_manifest_store_recovery_receipt=(
                historical_manifest_store_recovery_receipt
            ),
            historical_manifest_store_recovery_receipt_bytes=(
                historical_manifest_store_recovery_receipt_raw
            ),
            historical_manifest_store_recovery_receipt_path=(
                historical_manifest_store_recovery_receipt_relative_path
            ),
            historical_manifest_store_recovery_authority=(
                historical_manifest_store_recovery_authority
            ),
            historical_manifest_store_recovery_authority_bytes=(
                historical_manifest_store_recovery_authority_raw
            ),
            historical_manifest_store_recovery_authority_path=(
                historical_manifest_store_recovery_authority_relative_path
            ),
            historical_manifest_store_recovery_carrier_compressed_bytes=(
                historical_manifest_store_recovery_carrier_raw
            ),
            historical_manifest_store_recovery_carrier_compressed_path=(
                historical_manifest_store_recovery_carrier_relative_path
            ),
            historical_manifest_current_source_record_audit=(
                historical_source_record_audit
            ),
            historical_manifest_current_source_record_audit_bytes=(
                historical_source_record_audit_raw
            ),
            historical_manifest_current_source_record_audit_path=(
                historical_source_record_audit_relative_path
            ),
            historical_manifest_replay_archive_path=(
                historical_replay_archive_relative_path
            ),
            historical_manifest_replay_recipe_verifier=(
                historical_replay_recipe_verifier
            ),
        )
        report = materialized.report
        # Exact-current reused entries already remain valid under the ordinary
        # semantic loader, which resolves them by content pins rather than
        # their JSON storage keys.  Rewriting such a sidecar adds an archive
        # and a new-looking receipt without changing any reviewer judgment.
        # Refuse that churn by default; a rare storage-only migration must be
        # explicit and cannot be confused with a semantic review refresh.
        if (
            report["fresh_target_count"] == 0
            and report["retired_prior_payload_group_count"] == 0
            and report["historical_replay_reused_target_count"] == 0
            and not args.allow_all_reuse_rewrite
        ):
            print(
                f"{args.paper}: all current semantic targets already reuse exact "
                "evidence; no statement receipt or archive was written"
            )
            return 0
        if prior.present and archive_path is None:
            raise StatementReceiptReissueError(
                "--archive is required when replacing an existing statement sidecar"
            )
    except StatementReceiptReissueError as exc:
        print(f"{args.paper}: receipt reissue refused: {exc}", file=sys.stderr)
        return 1

    report = dict(materialized.report)
    report["dry_run"] = not args.write
    if args.write:
        # Recheck immediately before any replacement. The first load was
        # stable, but a concurrent cache refresh, map edit, or sidecar edit
        # after plan validation must not be converted into a write on stale
        # evidence.
        try:
            final_surface = current_statement_receipt_surface(paper_dir)
            final_prior = load_prior_sidecar(sidecar_path)
        except StatementReceiptReissueError as exc:
            print(
                f"{args.paper}: receipt reissue refused before write: {exc}",
                file=sys.stderr,
            )
            return 1
        if not _same_surface(surface, final_surface):
            print(
                f"{args.paper}: receipt reissue refused before write: current cache/map "
                "surface changed after plan validation",
                file=sys.stderr,
            )
            return 1
        if (
            prior.present != final_prior.present
            or prior.raw_sha256 != final_prior.raw_sha256
        ):
            print(
                f"{args.paper}: receipt reissue refused before write: prior sidecar bytes "
                "changed after plan validation",
                file=sys.stderr,
            )
            return 1
        if historical_replay_path is not None:
            try:
                final_historical_replay_raw = historical_replay_path.read_bytes()
            except OSError:
                print(
                    f"{args.paper}: receipt reissue refused before write: historical replay "
                    "artifact became unavailable",
                    file=sys.stderr,
                )
                return 1
            if final_historical_replay_raw != historical_replay_raw:
                print(
                    f"{args.paper}: receipt reissue refused before write: historical replay "
                    "artifact bytes changed after plan validation",
                    file=sys.stderr,
                )
                return 1
            assert historical_source_record_audit_path is not None
            assert historical_source_record_audit_raw is not None
            historical_input_pins: list[tuple[Path, bytes]] = [
                (historical_source_record_audit_path, historical_source_record_audit_raw)
            ]
            if historical_manifest_store_recovery_receipt_path is not None:
                assert historical_manifest_store_recovery_receipt_raw is not None
                assert historical_manifest_store_recovery_authority_path is not None
                assert historical_manifest_store_recovery_authority_raw is not None
                assert historical_manifest_store_recovery_carrier_path is not None
                assert historical_manifest_store_recovery_carrier_raw is not None
                historical_input_pins.extend(
                    [
                        (
                            historical_manifest_store_recovery_receipt_path,
                            historical_manifest_store_recovery_receipt_raw,
                        ),
                        (
                            historical_manifest_store_recovery_authority_path,
                            historical_manifest_store_recovery_authority_raw,
                        ),
                        (
                            historical_manifest_store_recovery_carrier_path,
                            historical_manifest_store_recovery_carrier_raw,
                        ),
                    ]
                )
                input_label = "historical recovered manifest-store or source-record audit"
            else:
                assert historical_manifest_carrier_path is not None
                assert historical_manifest_carrier_raw is not None
                assert historical_manifest_authority_path is not None
                assert historical_manifest_authority_raw is not None
                historical_input_pins.extend(
                    [
                        (historical_manifest_carrier_path, historical_manifest_carrier_raw),
                        (
                            historical_manifest_authority_path,
                            historical_manifest_authority_raw,
                        ),
                    ]
                )
                input_label = "historical manifest carrier, authority, or source-record audit"
            try:
                changed_inputs = any(
                    path.read_bytes() != raw for path, raw in historical_input_pins
                )
            except OSError:
                print(
                    f"{args.paper}: receipt reissue refused before write: {input_label} "
                    "became unavailable",
                    file=sys.stderr,
                )
                return 1
            if changed_inputs:
                print(
                    f"{args.paper}: receipt reissue refused before write: {input_label} "
                    "bytes changed after plan validation",
                    file=sys.stderr,
                )
                return 1
        # Archive first: if a later sidecar replace fails, the original exact
        # bytes remain recoverable. Each individual output is atomic.
        if materialized.archive is not None:
            assert archive_path is not None
            if archive_path.exists():
                print(
                    f"{args.paper}: receipt reissue refused before write: archive path already exists",
                    file=sys.stderr,
                )
                return 1
            _atomic_write(archive_path, _json_bytes(materialized.archive))
        _atomic_write(output_path, _json_bytes(materialized.sidecar))
        print(
            f"{args.paper}: wrote {report['fresh_target_count']} fresh and "
            f"{report['reused_target_count']} reused and "
            f"{report['historical_replay_reused_target_count']} historically transported "
            "statement receipts"
        )
    else:
        print(
            f"{args.paper}: receipt reissue plan validates ({report['fresh_target_count']} fresh, "
            f"{report['reused_target_count']} reused, "
            f"{report['historical_replay_reused_target_count']} historically transported); "
            "rerun with --write"
        )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
