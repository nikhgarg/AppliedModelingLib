"""Freeze and publish one current closeout plan from acquired typed inputs.

This module owns only immutable publication transport, file-mutation guards,
the non-authoritative compiled-input cache, and the operational plan receipt.
It does not discover Lean declarations, construct semantic judgments, choose
actions, run a worker, or grant final paper acceptance.
"""

from __future__ import annotations

import hashlib
import json
import os
import re
from dataclasses import dataclass, replace
from pathlib import Path
from typing import Any, Mapping

from scripts.closeout_execution_state import atomic_write_json
from scripts.closeout_plan_receipt import (
    CloseoutPlanReceiptError,
    build_closeout_plan_receipt,
    closeout_plan_receipt_path,
    validate_content_input_snapshot,
    validated_closeout_plan_receipt,
)


SHA256_RE = re.compile(r"^[0-9a-f]{64}$")
PLAN_RECEIPT_PUBLICATION_DISPOSITIONS = frozenset(
    {"published", "source_race", "compiled_race", "deterministic_input", "publication_io"}
)
COMPILED_INPUT_CACHE_SCHEMA = 1
COMPILED_INPUT_CACHE_FILE = "closeout_compiled_inputs.json"


def _canonical_json(value: object) -> str:
    return json.dumps(
        value,
        ensure_ascii=True,
        sort_keys=True,
        separators=(",", ":"),
        default=str,
    )


def _digest(value: object) -> str:
    return hashlib.sha256(_canonical_json(value).encode("utf-8")).hexdigest()


def _decoded_json_mapping(raw: str, label: str) -> dict[str, Any]:
    try:
        value = json.loads(raw)
    except json.JSONDecodeError as exc:
        raise ValueError(f"{label} is not valid JSON") from exc
    if not isinstance(value, dict):
        raise ValueError(f"{label} is not a JSON object")
    return value


def stat_identity(stat: os.stat_result) -> tuple[int, int, int, int, int]:
    """Return the short-lived local identity used only for race detection."""

    return (
        stat.st_dev,
        stat.st_ino,
        stat.st_size,
        stat.st_mtime_ns,
        stat.st_ctime_ns,
    )


def mutation_snapshot_is_current(snapshot: Mapping[str, object]) -> bool:
    """Recheck one acquired local file set without making it receipt identity."""

    expected: dict[str, tuple[int, int, int, int, int] | None] = {}
    current: dict[str, tuple[int, int, int, int, int] | None] = {}
    for raw_path, raw_value in snapshot.items():
        path = str(raw_path)
        if raw_value is None:
            expected[path] = None
        elif isinstance(raw_value, (list, tuple)) and len(raw_value) == 5:
            expected[path] = tuple(int(value) for value in raw_value)
        else:
            return False
        try:
            current[path] = stat_identity(Path(path).stat())
        except OSError:
            current[path] = None
    return current == expected


def closeout_plan_input_paths(
    root: Path,
    folder: Path,
    *,
    strict_transaction_content_snapshot: Mapping[str, object],
) -> tuple[list[Path], list[Path]]:
    """Select only current transaction and status acceptance inputs."""

    status_path = folder / "status.json"
    try:
        status_payload = json.loads(status_path.read_bytes())
    except (OSError, json.JSONDecodeError) as exc:
        raise CloseoutPlanReceiptError(
            f"could not acquire target closeout path configuration: {exc}"
        ) from exc
    if not isinstance(status_payload, Mapping):
        raise CloseoutPlanReceiptError("paper status is not an object")
    content_paths = {
        status_path,
        *(root / str(relative) for relative in strict_transaction_content_snapshot),
    }
    return sorted(content_paths, key=str), []


def _compiled_input_cache_path(folder: Path) -> Path:
    return folder / ".review_traces" / COMPILED_INPUT_CACHE_FILE


def _compiled_content_projection(value: object) -> dict[str, dict[str, Any]] | None:
    if not isinstance(value, Mapping):
        return None
    projection: dict[str, dict[str, Any]] = {}
    for raw_path, raw_identity in value.items():
        if not isinstance(raw_identity, Mapping):
            return None
        identity = {
            str(key): item for key, item in raw_identity.items() if key != "stat_guard"
        }
        if identity.get("state") not in {"present", "missing"}:
            return None
        projection[str(raw_path)] = identity
    return projection


def _load_compiled_input_cache(folder: Path) -> dict[str, dict[str, Any]] | None:
    try:
        payload = json.loads(
            _compiled_input_cache_path(folder).read_text(encoding="utf-8")
        )
    except (OSError, json.JSONDecodeError):
        return None
    if (
        not isinstance(payload, Mapping)
        or payload.get("schema") != COMPILED_INPUT_CACHE_SCHEMA
        or payload.get("acceptance_credential") is not False
        or payload.get("operational_scheduling_only") is not True
        or payload.get("paper") != folder.name
        or not isinstance(payload.get("compiled_inputs"), Mapping)
    ):
        return None
    inputs = {
        str(path): dict(identity) if isinstance(identity, Mapping) else identity
        for path, identity in payload["compiled_inputs"].items()
    }
    if (
        _compiled_content_projection(inputs) is None
        or payload.get("compiled_inputs_sha256") != _digest(inputs)
    ):
        return None
    return inputs


def _write_compiled_input_cache(
    folder: Path, compiled_inputs: Mapping[str, object]
) -> None:
    inputs = {
        str(path): dict(identity) if isinstance(identity, Mapping) else identity
        for path, identity in compiled_inputs.items()
    }
    if _compiled_content_projection(inputs) is None:
        return
    atomic_write_json(
        _compiled_input_cache_path(folder),
        {
            "schema": COMPILED_INPUT_CACHE_SCHEMA,
            "acceptance_credential": False,
            "operational_scheduling_only": True,
            "paper": folder.name,
            "compiled_inputs": inputs,
            "compiled_inputs_sha256": _digest(inputs),
        },
    )


@dataclass(frozen=True)
class CloseoutPlanPublicationInputs:
    """Paper-bound canonical snapshot for one publication attempt."""

    paper: str
    payload_json: str

    def __post_init__(self) -> None:
        if not self.paper.strip():
            raise ValueError("closeout publication inputs have no paper")
        payload = self.payload
        if set(payload) != {
            "audit_material_identity",
            "audit_material_sha256",
            "compiled_ledger",
            "final_holistic_audit_surface",
            "all_selected_semantic_review_sha256",
            "lean_closure_projection",
            "source_ledger",
            "strict_transaction_snapshot",
            "v11_lean_review_graph",
        }:
            raise ValueError("closeout publication inputs have malformed fields")
        if payload["audit_material_identity"] != "strict_transaction_content_snapshot":
            raise ValueError("closeout publication inputs have invalid material identity")
        if not SHA256_RE.fullmatch(str(payload["audit_material_sha256"])):
            raise ValueError("closeout publication inputs have invalid material digest")
        for value, label in (
            (payload["source_ledger"], "source mutation ledger"),
            (payload["compiled_ledger"], "compiled mutation ledger"),
            (payload["strict_transaction_snapshot"], "strict transaction snapshot"),
            (payload["lean_closure_projection"], "Lean closure projection"),
        ):
            if not isinstance(value, dict):
                raise ValueError(f"{label} is not a JSON object")
        for value, label in (
            (payload["v11_lean_review_graph"], "v11 Lean review graph"),
            (payload["final_holistic_audit_surface"], "final holistic audit surface"),
        ):
            if value is not None and not isinstance(value, dict):
                raise ValueError(f"{label} is not a JSON object")
        if _digest(payload["strict_transaction_snapshot"]) != str(
            payload["audit_material_sha256"]
        ):
            raise ValueError(
                "closeout publication inputs do not bind their strict transaction"
            )

    @classmethod
    def capture(
        cls,
        *,
        folder: Path,
        source_ledger: Mapping[str, object],
        compiled_ledger: Mapping[str, object],
        strict_transaction_snapshot: Mapping[str, object],
        lean_closure_projection: Mapping[str, object],
    ) -> CloseoutPlanPublicationInputs:
        strict_frozen = json.loads(_canonical_json(strict_transaction_snapshot))
        return cls(
            paper=folder.name,
            payload_json=_canonical_json(
                {
                    "audit_material_identity": "strict_transaction_content_snapshot",
                    "audit_material_sha256": _digest(strict_frozen),
                    "source_ledger": source_ledger,
                    "compiled_ledger": compiled_ledger,
                    "strict_transaction_snapshot": strict_frozen,
                    "lean_closure_projection": lean_closure_projection,
                    "v11_lean_review_graph": None,
                    "final_holistic_audit_surface": None,
                    "all_selected_semantic_review_sha256": "",
                }
            ),
        )

    def with_review_surfaces(
        self,
        *,
        v11_lean_review_graph: Mapping[str, object],
        final_holistic_audit_surface: Mapping[str, object],
        all_selected_semantic_review_sha256: str,
    ) -> CloseoutPlanPublicationInputs:
        if not SHA256_RE.fullmatch(all_selected_semantic_review_sha256):
            raise ValueError(
                "closeout publication inputs have no all-selected semantic-review identity"
            )
        payload = self.payload
        payload["v11_lean_review_graph"] = v11_lean_review_graph
        payload["final_holistic_audit_surface"] = final_holistic_audit_surface
        payload["all_selected_semantic_review_sha256"] = (
            all_selected_semantic_review_sha256
        )
        return replace(self, payload_json=_canonical_json(payload))

    @property
    def payload(self) -> dict[str, Any]:
        return _decoded_json_mapping(self.payload_json, "closeout publication inputs")

    @property
    def audit_material_identity(self) -> str:
        return str(self.payload["audit_material_identity"])

    @property
    def audit_material_sha256(self) -> str:
        return str(self.payload["audit_material_sha256"])

    def identity_payload(self) -> dict[str, object]:
        payload = self.payload
        return {
            "paper": self.paper,
            "source_ledger": payload["source_ledger"],
            "compiled_ledger": payload["compiled_ledger"],
            "strict_transaction_snapshot": payload["strict_transaction_snapshot"],
            "lean_closure_projection": payload["lean_closure_projection"],
            "v11_lean_review_graph": payload["v11_lean_review_graph"],
            "final_holistic_audit_surface": payload["final_holistic_audit_surface"],
            "all_selected_semantic_review_sha256": payload[
                "all_selected_semantic_review_sha256"
            ],
            "audit_material_sha256": self.audit_material_sha256,
        }


@dataclass(frozen=True)
class CurrentV11OperationalPlan:
    """An operator plan plus its separately frozen publication authority."""

    plan_json: str
    publication_inputs: CloseoutPlanPublicationInputs | None = None

    def __post_init__(self) -> None:
        _decoded_json_mapping(self.plan_json, "current v11 operator plan")

    @classmethod
    def capture(
        cls,
        plan: Mapping[str, object],
        *,
        publication_inputs: CloseoutPlanPublicationInputs | None = None,
    ) -> CurrentV11OperationalPlan:
        return cls(
            plan_json=_canonical_json(plan),
            publication_inputs=publication_inputs,
        )

    @property
    def plan(self) -> dict[str, Any]:
        return _decoded_json_mapping(self.plan_json, "current v11 operator plan")


@dataclass(frozen=True)
class CloseoutPlanReceiptPublication:
    """Result of attempting to freeze the exact strict-closeout input set."""

    receipt: dict[str, Any] | None
    error: str
    disposition: str
    input_identity_sha256: str

    def __post_init__(self) -> None:
        if self.disposition not in PLAN_RECEIPT_PUBLICATION_DISPOSITIONS:
            raise ValueError(
                "unknown closeout-plan receipt publication disposition: "
                + self.disposition
            )
        if not SHA256_RE.fullmatch(self.input_identity_sha256):
            raise ValueError("closeout-plan receipt publication has invalid input identity")


def publication_input_identity(
    *,
    folder: Path,
    publication_inputs: CloseoutPlanPublicationInputs | None,
) -> str:
    if publication_inputs is None:
        return _digest({"paper": folder.name, "publication_inputs": None})
    return _digest(publication_inputs.identity_payload())


def publish_closeout_plan_receipt(
    root: Path,
    plan: Mapping[str, Any],
    *,
    folder: Path,
    deep_paper_prose: bool,
    publication_inputs: CloseoutPlanPublicationInputs | None,
) -> CloseoutPlanReceiptPublication:
    """Publish one receipt without mutating or reacquiring planner inputs."""

    input_identity_sha256 = publication_input_identity(
        folder=folder,
        publication_inputs=publication_inputs,
    )

    def failed(error: str, disposition: str) -> CloseoutPlanReceiptPublication:
        return CloseoutPlanReceiptPublication(
            receipt=None,
            error=error,
            disposition=disposition,
            input_identity_sha256=input_identity_sha256,
        )

    if publication_inputs is None:
        return failed(
            "planner has no immutable publication input snapshot",
            "deterministic_input",
        )
    if publication_inputs.paper != folder.name:
        return failed(
            "planner publication inputs belong to another paper",
            "deterministic_input",
        )
    frozen_inputs = publication_inputs.payload
    source_ledger = frozen_inputs["source_ledger"]
    compiled_ledger = frozen_inputs["compiled_ledger"]
    strict_transaction_snapshot = frozen_inputs["strict_transaction_snapshot"]
    lean_closure_projection = frozen_inputs["lean_closure_projection"]
    v11_lean_review_graph = frozen_inputs["v11_lean_review_graph"]
    final_holistic_audit_surface = frozen_inputs["final_holistic_audit_surface"]
    all_selected_semantic_review_sha256 = frozen_inputs[
        "all_selected_semantic_review_sha256"
    ]
    if not mutation_snapshot_is_current(source_ledger):
        return failed("Lean source closure changed before plan publication", "source_race")
    if not mutation_snapshot_is_current(compiled_ledger):
        return failed(
            "compiled Lean closure changed before plan publication", "compiled_race"
        )
    if lean_closure_projection.get("state") != "present":
        return failed(
            "Lean-authored paper-root closure projection is unavailable",
            "deterministic_input",
        )
    if (
        publication_inputs.audit_material_identity
        != "strict_transaction_content_snapshot"
        or plan.get("audit_material_identity")
        != publication_inputs.audit_material_identity
    ):
        return failed(
            "current v11 plan has no selected semantic-transaction identity",
            "deterministic_input",
        )
    if (
        _digest(strict_transaction_snapshot)
        != publication_inputs.audit_material_sha256
        or str(plan.get("audit_material_sha256") or "")
        != publication_inputs.audit_material_sha256
    ):
        return failed(
            "planner semantic-transaction identity is malformed",
            "deterministic_input",
        )
    current_transaction, transaction_error = validate_content_input_snapshot(
        root,
        strict_transaction_snapshot,
    )
    if current_transaction is None:
        return failed(transaction_error, "source_race")
    strict_transaction_snapshot = current_transaction
    if not isinstance(v11_lean_review_graph, Mapping):
        return failed(
            "planner has no exact v11 Lean review graph", "deterministic_input"
        )
    if not isinstance(final_holistic_audit_surface, Mapping):
        return failed(
            "planner has no typed final holistic audit surface", "deterministic_input"
        )
    try:
        content_paths, stat_paths = closeout_plan_input_paths(
            root,
            folder,
            strict_transaction_content_snapshot=strict_transaction_snapshot,
        )
        receipt = build_closeout_plan_receipt(
            root,
            paper=folder.name,
            deep_paper_prose=deep_paper_prose,
            content_paths=content_paths,
            stat_paths=stat_paths,
            source_ledger=source_ledger,
            compiled_ledger=compiled_ledger,
            lean_import_closure_projection=lean_closure_projection,
            lean_import_closure_projection_validated=True,
            v11_lean_review_graph=v11_lean_review_graph,
            final_holistic_audit_surface=final_holistic_audit_surface,
            all_selected_semantic_review_sha256=(
                str(all_selected_semantic_review_sha256)
            ),
            reusable_content_inputs=strict_transaction_snapshot,
            reusable_compiled_inputs=_load_compiled_input_cache(folder),
        )
    except CloseoutPlanReceiptError as exc:
        return failed(str(exc), "deterministic_input")
    except (OSError, RuntimeError, ValueError) as exc:
        return failed(str(exc), "publication_io")
    receipt_identity = str(receipt["plan_identity_sha256"])
    path = closeout_plan_receipt_path(root, folder.name, receipt_identity)
    try:
        atomic_write_json(path, receipt)
        published = json.loads(path.read_text(encoding="utf-8"))
        if published != receipt:
            raise CloseoutPlanReceiptError(
                "published closeout plan receipt does not equal this planner's receipt"
            )
        validated_closeout_plan_receipt(
            root,
            published,
            paper=folder.name,
            deep_paper_prose=deep_paper_prose,
            expected_plan_identity=receipt_identity,
        )
        raw_compiled_inputs = receipt.get("compiled_inputs")
        if isinstance(raw_compiled_inputs, Mapping):
            _write_compiled_input_cache(folder, raw_compiled_inputs)
    except OSError as exc:
        return failed(str(exc), "publication_io")
    except (CloseoutPlanReceiptError, json.JSONDecodeError) as exc:
        return failed(str(exc), "deterministic_input")
    if not mutation_snapshot_is_current(source_ledger):
        return failed("Lean source closure changed during plan publication", "source_race")
    if not mutation_snapshot_is_current(compiled_ledger):
        return failed(
            "compiled Lean closure changed during plan publication", "compiled_race"
        )
    return CloseoutPlanReceiptPublication(
        receipt=receipt,
        error="",
        disposition="published",
        input_identity_sha256=input_identity_sha256,
    )
