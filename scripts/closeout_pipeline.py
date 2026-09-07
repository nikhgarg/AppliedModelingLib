#!/usr/bin/env python3
"""Shared typed closeout context and non-authoritative stage DAG.

This module is the deliberately small coordination core for paper closeout.
It does not replace any semantic, source, Lean, build, or final-receipt gate.
Instead it gives producers and consumers one immutable interpretation of the
route ledger and one content-addressed scheduling graph.  The final integrated
audit remains the only authority that can accept a paper.
"""

from __future__ import annotations

import hashlib
import json
import os
import re
import tempfile
from dataclasses import dataclass
from enum import Enum
from pathlib import Path
from types import MappingProxyType
from typing import Any, Iterable, Mapping, Sequence

try:
    from scripts.closeout_content_store import (
        CloseoutContentStoreError,
        canonical_json_bytes,
        content_sha256,
        load_closeout_object,
        store_closeout_object,
    )
    from scripts.obligation_routes import (
        EvidenceRoute,
        EvidenceRouteSet,
        ObligationRouteError as CloseoutPipelineError,
        RouteKind,
        SemanticReviewTargetKind,
        semantic_review_target,
        typed_route_validation_required,
    )
    from scripts.closeout_status_projection import (
        CloseoutStatusProjectionError,
        paper_status_acceptance_projection,
    )
except ModuleNotFoundError:  # Direct ``python scripts/...`` execution.
    from closeout_content_store import (
        CloseoutContentStoreError,
        canonical_json_bytes,
        content_sha256,
        load_closeout_object,
        store_closeout_object,
    )
    from obligation_routes import (
        EvidenceRoute,
        EvidenceRouteSet,
        ObligationRouteError as CloseoutPipelineError,
        RouteKind,
        SemanticReviewTargetKind,
        semantic_review_target,
        typed_route_validation_required,
    )
    from closeout_status_projection import (
        CloseoutStatusProjectionError,
        paper_status_acceptance_projection,
    )


SHA256_RE = re.compile(r"^[0-9a-f]{64}$")
CLOSEOUT_CONTEXT_SCHEMA = 2
CLOSEOUT_STAGE_RECEIPT_SCHEMA = 1
CLOSEOUT_STAGE_DIRECTORY = Path(".review_traces") / "closeout_stages"


class CloseoutStage(str, Enum):
    SOURCE_CLAIM_INVENTORY = "source_claim_inventory"
    SOURCE_SPEC_CORRESPONDENCE = "source_spec_correspondence"
    RAW_SOURCE_RECORD = "raw_source_record"
    SEMANTIC_MATERIALIZATION = "semantic_materialization"
    ROUTE_SCHEMA_PREFLIGHT = "route_schema_preflight"
    LEAN_ATTESTATION = "lean_attestation"
    STRICT_INTEGRATION = "strict_integration"
    FOCUSED_BUILD = "focused_build"
    CANONICAL_RECEIPT = "canonical_receipt"


STAGE_DEPENDENCIES: Mapping[CloseoutStage, tuple[CloseoutStage, ...]] = (
    MappingProxyType(
        {
            CloseoutStage.SOURCE_CLAIM_INVENTORY: (),
            CloseoutStage.SOURCE_SPEC_CORRESPONDENCE: (
                CloseoutStage.SOURCE_CLAIM_INVENTORY,
            ),
            CloseoutStage.RAW_SOURCE_RECORD: (
                CloseoutStage.SOURCE_SPEC_CORRESPONDENCE,
            ),
            CloseoutStage.SEMANTIC_MATERIALIZATION: (
                CloseoutStage.RAW_SOURCE_RECORD,
            ),
            CloseoutStage.ROUTE_SCHEMA_PREFLIGHT: (
                CloseoutStage.SEMANTIC_MATERIALIZATION,
            ),
            CloseoutStage.LEAN_ATTESTATION: (
                CloseoutStage.ROUTE_SCHEMA_PREFLIGHT,
            ),
            CloseoutStage.STRICT_INTEGRATION: (
                CloseoutStage.LEAN_ATTESTATION,
            ),
            CloseoutStage.FOCUSED_BUILD: (
                CloseoutStage.STRICT_INTEGRATION,
            ),
            CloseoutStage.CANONICAL_RECEIPT: (
                CloseoutStage.FOCUSED_BUILD,
            ),
        }
    )
)


def _digest(value: object) -> str:
    return content_sha256(value)


def _validated_sha(value: object, field: str) -> str:
    text = str(value or "").strip().lower()
    if not SHA256_RE.fullmatch(text):
        raise CloseoutPipelineError(f"{field} is not a lowercase SHA-256 digest")
    return text


@dataclass(frozen=True)
class CloseoutContext:
    """Immutable, content-addressed view shared by planner and strict worker."""

    paper: str
    plan_identity_sha256: str
    source_map_sha256: str
    status_sha256: str
    route_set_sha256: str
    route_object: Mapping[str, Any]
    content_inputs_sha256: str
    compiled_inputs_sha256: str
    lean_closure_sha256: str
    protocol_sha256: str
    context_sha256: str

    def projection(self) -> dict[str, Any]:
        return {
            "schema": CLOSEOUT_CONTEXT_SCHEMA,
            "acceptance_credential": False,
            "operational_scheduling_only": True,
            "paper": self.paper,
            "plan_identity_sha256": self.plan_identity_sha256,
            "source_map_sha256": self.source_map_sha256,
            "status_sha256": self.status_sha256,
            "route_set_sha256": self.route_set_sha256,
            "route_object": dict(self.route_object),
            "content_inputs_sha256": self.content_inputs_sha256,
            "compiled_inputs_sha256": self.compiled_inputs_sha256,
            "lean_closure_sha256": self.lean_closure_sha256,
            "protocol_sha256": self.protocol_sha256,
            "context_sha256": self.context_sha256,
        }


def _receipt_file_sha(receipt: Mapping[str, Any], relative: str) -> str:
    raw = receipt.get("content_inputs")
    identity = raw.get(relative) if isinstance(raw, Mapping) else None
    if not isinstance(identity, Mapping) or identity.get("state") != "present":
        raise CloseoutPipelineError(f"closeout plan does not bind {relative}")
    return _validated_sha(identity.get("sha256"), f"{relative} receipt SHA")


def build_closeout_context(
    root: Path,
    folder: Path,
    *,
    plan_receipt: Mapping[str, Any],
    engine_registration: Mapping[str, Any],
    lean_closure_projection: object,
) -> CloseoutContext:
    """Build one exact context and verify its direct paper bytes are plan-bound."""

    root = root.resolve()
    folder = folder.resolve()
    try:
        paper_relative = folder.relative_to(root).as_posix()
    except ValueError as exc:
        raise CloseoutPipelineError("paper folder escapes repository") from exc
    paper = folder.name
    if plan_receipt.get("paper") != paper:
        raise CloseoutPipelineError("closeout plan belongs to another paper")
    map_relative = f"{paper_relative}/audit/paper_statement_map.json"
    status_relative = f"{paper_relative}/status.json"
    try:
        map_bytes = (root / map_relative).read_bytes()
        status_bytes = (root / status_relative).read_bytes()
        source_map = json.loads(map_bytes)
        json.loads(status_bytes)
    except (OSError, json.JSONDecodeError) as exc:
        raise CloseoutPipelineError(f"could not acquire closeout context: {exc}") from exc
    map_sha = hashlib.sha256(map_bytes).hexdigest()
    status_sha = hashlib.sha256(status_bytes).hexdigest()
    if map_sha != _receipt_file_sha(plan_receipt, map_relative):
        raise CloseoutPipelineError("statement map changed after plan receipt")
    if "target_paper_status_projection" in plan_receipt:
        try:
            current_status_projection = paper_status_acceptance_projection(root, paper)
        except CloseoutStatusProjectionError as exc:
            raise CloseoutPipelineError(str(exc)) from exc
        if current_status_projection != plan_receipt.get(
            "target_paper_status_projection"
        ):
            raise CloseoutPipelineError(
                "paper status acceptance configuration changed after plan receipt"
            )
        status_sha = _digest(current_status_projection)
    elif status_sha != _receipt_file_sha(plan_receipt, status_relative):
        raise CloseoutPipelineError("paper status changed after plan receipt")
    route_set = EvidenceRouteSet.from_source_map(source_map)
    route_reference = store_closeout_object(
        root, route_set.projection(), kind="typed_evidence_routes"
    )
    if load_closeout_object(
        root, route_reference, expected_kind="typed_evidence_routes"
    ) != route_set.projection():
        raise CloseoutPipelineError("typed route object did not round-trip")
    protocol = plan_receipt.get("strict_closeout_protocol_projection")
    protocol_sha = _digest(protocol)
    engine_tree = _validated_sha(
        engine_registration.get("engine_tree_sha256"), "registered engine tree"
    )
    sequence = engine_registration.get("revision_sequence")
    if not isinstance(sequence, int) or isinstance(sequence, bool) or sequence < 1:
        raise CloseoutPipelineError("registered engine revision sequence is invalid")
    # The caller must prove that the executing engine is clean and registered,
    # but implementation provenance is not a paper or scheduling identity.
    # Keeping it out of the context lets unchanged source/Lean/review work
    # survive arbitrarily many registered implementation-only revisions.
    del engine_tree, sequence
    material = {
        "paper": paper,
        "plan_identity_sha256": _validated_sha(
            plan_receipt.get("plan_identity_sha256"), "plan identity"
        ),
        "source_map_sha256": map_sha,
        "status_sha256": status_sha,
        "route_set_sha256": route_set.sha256,
        "route_object_sha256": route_reference["sha256"],
        "content_inputs_sha256": _digest(plan_receipt.get("content_inputs")),
        "compiled_inputs_sha256": _digest(plan_receipt.get("compiled_inputs")),
        "lean_closure_sha256": _digest(lean_closure_projection),
        "protocol_sha256": protocol_sha,
    }
    return CloseoutContext(
        paper=paper,
        plan_identity_sha256=material["plan_identity_sha256"],
        source_map_sha256=map_sha,
        status_sha256=status_sha,
        route_set_sha256=route_set.sha256,
        route_object=MappingProxyType(dict(route_reference)),
        content_inputs_sha256=material["content_inputs_sha256"],
        compiled_inputs_sha256=material["compiled_inputs_sha256"],
        lean_closure_sha256=material["lean_closure_sha256"],
        protocol_sha256=protocol_sha,
        context_sha256=_digest(material),
    )


@dataclass(frozen=True)
class StageReceipt:
    stage: CloseoutStage
    paper: str
    context_sha256: str
    input_sha256: str
    dependency_receipt_sha256s: tuple[tuple[str, str], ...]
    output_object: Mapping[str, Any]
    metrics: Mapping[str, Any]
    receipt_sha256: str

    def projection(self) -> dict[str, Any]:
        return {
            "schema": CLOSEOUT_STAGE_RECEIPT_SCHEMA,
            "acceptance_credential": False,
            "operational_scheduling_only": True,
            "stage": self.stage.value,
            "paper": self.paper,
            "context_sha256": self.context_sha256,
            "input_sha256": self.input_sha256,
            "dependency_receipt_sha256s": {
                stage: digest for stage, digest in self.dependency_receipt_sha256s
            },
            "output_object": dict(self.output_object),
            "metrics": dict(self.metrics),
            "receipt_sha256": self.receipt_sha256,
        }


def _atomic_json(path: Path, payload: Mapping[str, Any]) -> None:
    data = json.dumps(payload, indent=2, sort_keys=True).encode("utf-8") + b"\n"
    path.parent.mkdir(parents=True, exist_ok=True)
    fd, raw_temp = tempfile.mkstemp(
        prefix=f".{path.name}.", suffix=".tmp", dir=path.parent
    )
    temp = Path(raw_temp)
    try:
        with os.fdopen(fd, "wb") as stream:
            stream.write(data)
            stream.flush()
            os.fsync(stream.fileno())
        os.replace(temp, path)
    finally:
        try:
            temp.unlink()
        except FileNotFoundError:
            pass


def issue_stage_receipt(
    root: Path,
    folder: Path,
    *,
    context: CloseoutContext,
    stage: CloseoutStage,
    dependencies: Mapping[CloseoutStage, StageReceipt],
    output: object,
    metrics: Mapping[str, Any] | None = None,
) -> StageReceipt:
    """Issue a compact operational receipt after exact dependency validation."""

    expected = STAGE_DEPENDENCIES[stage]
    if set(dependencies) != set(expected):
        raise CloseoutPipelineError(
            f"{stage.value} requires exactly {[item.value for item in expected]}"
        )
    dependency_pairs: list[tuple[str, str]] = []
    for dependency in expected:
        receipt = dependencies[dependency]
        if (
            receipt.stage is not dependency
            or receipt.paper != context.paper
            or receipt.context_sha256 != context.context_sha256
        ):
            raise CloseoutPipelineError("stage dependency belongs to another context")
        dependency_pairs.append((dependency.value, receipt.receipt_sha256))
    output_reference = store_closeout_object(
        root, output, kind=f"closeout_stage_{stage.value}"
    )
    input_material = {
        "stage": stage.value,
        "paper": context.paper,
        "context_sha256": context.context_sha256,
        "dependencies": dict(dependency_pairs),
    }
    input_sha = _digest(input_material)
    material = {
        **input_material,
        "input_sha256": input_sha,
        "output_object": output_reference,
        "metrics": dict(metrics or {}),
    }
    receipt = StageReceipt(
        stage=stage,
        paper=context.paper,
        context_sha256=context.context_sha256,
        input_sha256=input_sha,
        dependency_receipt_sha256s=tuple(dependency_pairs),
        output_object=MappingProxyType(dict(output_reference)),
        metrics=MappingProxyType(dict(metrics or {})),
        receipt_sha256=_digest(material),
    )
    directory = folder / CLOSEOUT_STAGE_DIRECTORY
    immutable_path = directory / f"{stage.value}.{receipt.receipt_sha256}.json"
    current_path = directory / f"{stage.value}.current.json"
    projection = receipt.projection()
    _atomic_json(immutable_path, projection)
    _atomic_json(current_path, projection)
    return receipt


def validated_stage_receipt(
    root: Path,
    value: object,
    *,
    context: CloseoutContext,
    stage: CloseoutStage,
) -> StageReceipt:
    if not isinstance(value, Mapping):
        raise CloseoutPipelineError("stage receipt is not an object")
    required = {
        "schema",
        "acceptance_credential",
        "operational_scheduling_only",
        "stage",
        "paper",
        "context_sha256",
        "input_sha256",
        "dependency_receipt_sha256s",
        "output_object",
        "metrics",
        "receipt_sha256",
    }
    if set(value) != required:
        raise CloseoutPipelineError("stage receipt fields are malformed")
    raw_dependencies = value.get("dependency_receipt_sha256s")
    if not isinstance(raw_dependencies, Mapping):
        raise CloseoutPipelineError("stage receipt dependencies are malformed")
    expected = STAGE_DEPENDENCIES[stage]
    if set(raw_dependencies) != {item.value for item in expected}:
        raise CloseoutPipelineError("stage receipt dependency set is incomplete")
    dependency_pairs = tuple(
        (dependency.value, _validated_sha(raw_dependencies[dependency.value], "dependency receipt"))
        for dependency in expected
    )
    if (
        value.get("schema") != CLOSEOUT_STAGE_RECEIPT_SCHEMA
        or value.get("acceptance_credential") is not False
        or value.get("operational_scheduling_only") is not True
        or value.get("stage") != stage.value
        or value.get("paper") != context.paper
        or value.get("context_sha256") != context.context_sha256
        or not isinstance(value.get("metrics"), Mapping)
    ):
        raise CloseoutPipelineError("stage receipt does not match the current context")
    input_material = {
        "stage": stage.value,
        "paper": context.paper,
        "context_sha256": context.context_sha256,
        "dependencies": dict(dependency_pairs),
    }
    input_sha = _digest(input_material)
    if value.get("input_sha256") != input_sha:
        raise CloseoutPipelineError("stage receipt input identity is corrupt")
    output = load_closeout_object(
        root, value.get("output_object"), expected_kind=f"closeout_stage_{stage.value}"
    )
    material = {
        **input_material,
        "input_sha256": input_sha,
        "output_object": dict(value["output_object"]),
        "metrics": dict(value["metrics"]),
    }
    receipt_sha = _digest(material)
    if value.get("receipt_sha256") != receipt_sha:
        raise CloseoutPipelineError("stage receipt integrity is corrupt")
    # Force the object read above even though the receipt retains only its ref.
    del output
    return StageReceipt(
        stage=stage,
        paper=context.paper,
        context_sha256=context.context_sha256,
        input_sha256=input_sha,
        dependency_receipt_sha256s=dependency_pairs,
        output_object=MappingProxyType(dict(value["output_object"])),
        metrics=MappingProxyType(dict(value["metrics"])),
        receipt_sha256=receipt_sha,
    )


def current_stage_receipts(
    root: Path, folder: Path, *, context: CloseoutContext
) -> dict[CloseoutStage, StageReceipt]:
    """Load only the contiguous current prefix of the stage DAG."""

    current: dict[CloseoutStage, StageReceipt] = {}
    for stage in CloseoutStage:
        path = folder / CLOSEOUT_STAGE_DIRECTORY / f"{stage.value}.current.json"
        try:
            payload = json.loads(path.read_text(encoding="utf-8"))
            receipt = validated_stage_receipt(
                root, payload, context=context, stage=stage
            )
        except (OSError, json.JSONDecodeError, CloseoutContentStoreError, CloseoutPipelineError):
            break
        if any(current.get(dependency) is None for dependency in STAGE_DEPENDENCIES[stage]):
            break
        if any(
            dict(receipt.dependency_receipt_sha256s).get(dependency.value)
            != current[dependency].receipt_sha256
            for dependency in STAGE_DEPENDENCIES[stage]
        ):
            break
        current[stage] = receipt
    return current


def stage_dag_projection(
    receipts: Mapping[CloseoutStage, StageReceipt],
) -> dict[str, Any]:
    """Return a compact human- and machine-inspectable scheduling projection."""

    first_pending = next((stage for stage in CloseoutStage if stage not in receipts), None)
    return {
        "schema": 1,
        "acceptance_credential": False,
        "operational_scheduling_only": True,
        "current_prefix_length": len(receipts),
        "next_stage": first_pending.value if first_pending is not None else None,
        "stages": [
            {
                "id": stage.value,
                "dependencies": [item.value for item in STAGE_DEPENDENCIES[stage]],
                "state": "current" if stage in receipts else "pending",
                **(
                    {"receipt_sha256": receipts[stage].receipt_sha256}
                    if stage in receipts
                    else {}
                ),
            }
            for stage in CloseoutStage
        ],
    }


def issue_observed_stage_prefix(
    root: Path,
    folder: Path,
    *,
    context: CloseoutContext,
    observed_outputs: Mapping[CloseoutStage, object],
    metrics: Mapping[CloseoutStage, Mapping[str, Any]] | None = None,
) -> dict[CloseoutStage, StageReceipt]:
    """Issue an exact contiguous prefix; never infer or bridge a missing stage."""

    issued = current_stage_receipts(root, folder, context=context)
    metrics = metrics or {}
    for stage in CloseoutStage:
        if stage in issued:
            continue
        if stage not in observed_outputs:
            break
        dependencies = {
            dependency: issued[dependency] for dependency in STAGE_DEPENDENCIES[stage]
        }
        issued[stage] = issue_stage_receipt(
            root,
            folder,
            context=context,
            stage=stage,
            dependencies=dependencies,
            output=observed_outputs[stage],
            metrics=metrics.get(stage),
        )
    return issued
