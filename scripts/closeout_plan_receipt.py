#!/usr/bin/env python3
"""Target-scoped operational input receipts for durable paper closeout.

These ignored receipts prevent a stale printed launcher command from
suppressing or starting a closeout after its paper inputs changed.  They are
operational scheduling data only and never count as semantic audit evidence.
"""

from __future__ import annotations

import hashlib
import json
import os
import re
import stat as stat_module
from pathlib import Path
from typing import Any, Callable, Iterable, Mapping

try:
    from scripts.closeout_content_store import (
        CloseoutContentStoreError,
        is_closeout_object_reference,
        load_closeout_object,
        store_closeout_object,
    )
except ModuleNotFoundError:  # Direct ``python scripts/...`` execution.
    from closeout_content_store import (
        CloseoutContentStoreError,
        is_closeout_object_reference,
        load_closeout_object,
        store_closeout_object,
    )

try:
    from scripts.portable_evidence_identity import (
        PortableEvidenceIdentityError,
        portable_evidence_sha256,
        portable_lean_closure_identity,
    )
except ModuleNotFoundError:  # Direct ``python scripts/...`` execution.
    from portable_evidence_identity import (
        PortableEvidenceIdentityError,
        portable_evidence_sha256,
        portable_lean_closure_identity,
    )

try:
    from scripts.closeout_status_projection import (
        CloseoutStatusProjectionError,
        paper_status_acceptance_projection,
    )
except ModuleNotFoundError:  # Direct ``python scripts/...`` execution.
    from closeout_status_projection import (
        CloseoutStatusProjectionError,
        paper_status_acceptance_projection,
    )

try:
    from scripts.final_holistic_audit_surface import (
        FinalHolisticAuditSurfaceError,
        build_final_holistic_audit_surface_from_repository,
        final_holistic_audit_surface_contract_is_supported,
        final_holistic_audit_surface_sha256,
    )
except ModuleNotFoundError:  # Direct ``python scripts/...`` execution.
    from final_holistic_audit_surface import (
        FinalHolisticAuditSurfaceError,
        build_final_holistic_audit_surface_from_repository,
        final_holistic_audit_surface_contract_is_supported,
        final_holistic_audit_surface_sha256,
    )

CLOSEOUT_PLAN_RECEIPT_SCHEMA = 7
SUPPORTED_CLOSEOUT_PLAN_RECEIPT_SCHEMAS = frozenset({2, 3, 4, 5, 6, 7})
CLOSEOUT_PLAN_RECEIPT_FILE = "closeout_execution_plan.json"
OPERATIONAL_PLAN_IDENTITY_SCHEMA = "closeout-execution-input-graph-v7"
PREVIOUS_OPERATIONAL_PLAN_IDENTITY_SCHEMA = "closeout-execution-input-graph-v6"
SCHEMA5_OPERATIONAL_PLAN_IDENTITY_SCHEMA = "closeout-execution-input-graph-v5"
SCHEMA4_OPERATIONAL_PLAN_IDENTITY_SCHEMA = "closeout-execution-input-graph-v4"
LEGACY_OPERATIONAL_PLAN_IDENTITY_SCHEMA = "closeout-execution-input-graph-v3"
LEAN_CLOSURE_OPERATIONAL_PROJECTION_SCHEMA = 1
SHA256_RE = re.compile(r"^[0-9a-f]{64}$")
PAPER_ID_RE = re.compile(r"^[A-Z][A-Za-z0-9]*\d{2}[A-Za-z0-9]*$")


class CloseoutPlanReceiptError(ValueError):
    """The ignored closeout plan receipt is absent, malformed, or stale."""


def resolved_plan_lean_closure_projection(
    root: Path, receipt: Mapping[str, object]
) -> dict[str, Any]:
    """Return the exact large Lean-closure payload bound by a plan receipt.

    Schema 2 embedded the payload in every receipt. Schema 3 stores the same
    canonical JSON once and retains a compact SHA-256 reference. Reading either
    form performs the same downstream validation; the reference is only a
    storage optimization and never an acceptance shortcut.
    """

    raw = receipt.get("lean_import_closure_projection")
    if is_closeout_object_reference(raw, kind="lean_import_closure_projection"):
        try:
            loaded = load_closeout_object(
                root,
                raw,
                expected_kind="lean_import_closure_projection",
            )
        except CloseoutContentStoreError as exc:
            raise CloseoutPlanReceiptError(str(exc)) from exc
        if not isinstance(loaded, Mapping):
            raise CloseoutPlanReceiptError(
                "stored Lean import-closure projection is not an object"
            )
        return dict(loaded)
    if receipt.get("schema") == 2 and isinstance(raw, Mapping):
        return dict(raw)
    raise CloseoutPlanReceiptError(
        "closeout plan has no valid Lean import-closure projection reference"
    )


def resolved_plan_v11_lean_review_graph(
    root: Path, receipt: Mapping[str, object]
) -> dict[str, Any] | None:
    """Load the plan's optional Lean graph scheduling carrier exactly once."""

    raw = receipt.get("v11_lean_review_graph")
    if raw is None:
        return None
    if not is_closeout_object_reference(raw, kind="v11_lean_review_graph"):
        raise CloseoutPlanReceiptError(
            "closeout plan has a malformed v11 Lean review graph reference"
        )
    try:
        loaded = load_closeout_object(
            root,
            raw,
            expected_kind="v11_lean_review_graph",
        )
    except CloseoutContentStoreError as exc:
        raise CloseoutPlanReceiptError(str(exc)) from exc
    if not isinstance(loaded, Mapping):
        raise CloseoutPlanReceiptError(
            "stored v11 Lean review graph carrier is not an object"
        )
    if (
        loaded.get("acceptance_credential") is not False
        or loaded.get("operational_scheduling_only") is not True
        or loaded.get("paper") != receipt.get("paper")
    ):
        raise CloseoutPlanReceiptError(
            "stored v11 Lean review graph carrier belongs to another closeout"
        )
    return dict(loaded)


def resolved_plan_final_holistic_audit_surface(
    root: Path, receipt: Mapping[str, object]
) -> dict[str, Any] | None:
    """Load the optional location-neutral final-audit surface."""

    raw = receipt.get("final_holistic_audit_surface")
    if raw is None:
        return None
    if not is_closeout_object_reference(raw, kind="final_holistic_audit_surface"):
        raise CloseoutPlanReceiptError(
            "closeout plan has a malformed final holistic audit surface reference"
        )
    try:
        loaded = load_closeout_object(
            root,
            raw,
            expected_kind="final_holistic_audit_surface",
        )
    except CloseoutContentStoreError as exc:
        raise CloseoutPlanReceiptError(str(exc)) from exc
    if not isinstance(loaded, Mapping):
        raise CloseoutPlanReceiptError(
            "stored final holistic audit surface is not an object"
        )
    if (
        not final_holistic_audit_surface_contract_is_supported(loaded)
        or loaded.get("paper") != receipt.get("paper")
    ):
        raise CloseoutPlanReceiptError(
            "stored final holistic audit surface belongs to another closeout"
        )
    recorded = str(
        receipt.get("final_holistic_audit_surface_sha256") or ""
    ).strip().lower()
    if (
        not SHA256_RE.fullmatch(recorded)
        or final_holistic_audit_surface_sha256(loaded) != recorded
    ):
        raise CloseoutPlanReceiptError(
            "stored final holistic audit surface identity is corrupt"
        )
    return dict(loaded)


def closeout_plan_receipt_path(root: Path, paper: str, plan_identity: str = "") -> Path:
    """Return a receipt path that cannot be clobbered by another plan identity."""

    filename = CLOSEOUT_PLAN_RECEIPT_FILE
    if plan_identity:
        if not SHA256_RE.fullmatch(plan_identity):
            raise CloseoutPlanReceiptError(
                "closeout plan receipt path requires a lowercase SHA-256 identity"
            )
        filename = f"closeout_execution_plan.{plan_identity}.json"
    return root / "papers" / paper / ".review_traces" / filename


def _stable_digest(value: object) -> str:
    return hashlib.sha256(
        json.dumps(
            value,
            ensure_ascii=True,
            sort_keys=True,
            separators=(",", ":"),
            default=str,
        ).encode("utf-8")
    ).hexdigest()


def _stat_identity(stat: os.stat_result) -> list[int]:
    return [
        stat.st_dev,
        stat.st_ino,
        stat.st_size,
        stat.st_mtime_ns,
        stat.st_ctime_ns,
    ]


def _logical_absolute(root: Path, path: Path) -> Path:
    candidate = path if path.is_absolute() else root / path
    return Path(os.path.abspath(candidate))


def _repository_relative(root: Path, path: Path) -> str:
    """Return a lexical repository path without erasing symlink identity."""

    try:
        return _logical_absolute(root, path).relative_to(root.resolve()).as_posix()
    except (OSError, RuntimeError, ValueError) as exc:
        raise CloseoutPlanReceiptError(
            f"closeout input escapes the repository: {path}"
        ) from exc


def _resolved_repository_relative(root: Path, path: Path) -> str:
    try:
        return path.resolve(strict=False).relative_to(root.resolve()).as_posix()
    except (OSError, RuntimeError, ValueError) as exc:
        raise CloseoutPlanReceiptError(
            f"closeout input resolves outside the repository: {path}"
        ) from exc


def _logical_path_projection(root: Path, path: Path) -> dict[str, Any]:
    """Bind a logical path, its symlink spelling, and its resolved target."""

    logical = _logical_absolute(root, path)
    resolved = _resolved_repository_relative(root, logical)
    try:
        link_stat = logical.lstat()
    except FileNotFoundError:
        return {"logical_state": "missing", "resolved_path": resolved}
    except OSError as exc:
        raise CloseoutPlanReceiptError(
            f"could not inspect closeout input {_repository_relative(root, logical)}: {exc}"
        ) from exc
    kind = stat_module.S_IFMT(link_stat.st_mode)
    if stat_module.S_ISLNK(link_stat.st_mode):
        try:
            link_target = os.readlink(logical)
        except OSError as exc:
            raise CloseoutPlanReceiptError(
                f"could not read closeout input symlink "
                f"{_repository_relative(root, logical)}: {exc}"
            ) from exc
        return {
            "logical_state": "symlink",
            "link_target": link_target,
            "resolved_path": resolved,
        }
    return {
        "logical_state": "regular"
        if stat_module.S_ISREG(link_stat.st_mode)
        else "other",
        "file_type": kind,
        "resolved_path": resolved,
    }


def _content_snapshot(
    root: Path,
    paths: Iterable[Path],
    *,
    reusable: Mapping[str, object] | None = None,
) -> dict[str, dict[str, Any]]:
    """Bind exact content bytes, using stat guards only as read accelerators."""

    snapshot: dict[str, dict[str, Any]] = {}
    logical_paths = {_logical_absolute(root, candidate) for candidate in paths}
    reusable = reusable or {}
    for path in sorted(logical_paths, key=str):
        relative = _repository_relative(root, path)
        link_before = _logical_path_projection(root, path)
        prior = reusable.get(relative)
        try:
            current_stat = path.stat()
        except FileNotFoundError:
            link_after = _logical_path_projection(root, path)
            if link_after != link_before:
                raise CloseoutPlanReceiptError(
                    f"closeout input changed while it was read: {relative}"
                )
            snapshot[relative] = {
                "state": "missing",
                "path": link_after,
                "sha256": None,
                "stat_guard": None,
            }
            continue
        except OSError as exc:
            raise CloseoutPlanReceiptError(
                f"could not inspect closeout input {relative}: {exc}"
            ) from exc
        current_guard = _stat_identity(current_stat)
        if (
            isinstance(prior, Mapping)
            and prior.get("state") == "present"
            and prior.get("path") == link_before
            and prior.get("stat_guard") == current_guard
            and isinstance(prior.get("byte_length"), int)
            and SHA256_RE.fullmatch(str(prior.get("sha256") or ""))
        ):
            snapshot[relative] = dict(prior)
            continue

        try:
            with path.open("rb") as stream:
                before = os.fstat(stream.fileno())
                content = stream.read()
                after = os.fstat(stream.fileno())
        except OSError as exc:
            raise CloseoutPlanReceiptError(
                f"could not read closeout input {relative}: {exc}"
            ) from exc
        link_after = _logical_path_projection(root, path)
        try:
            named_after = path.stat()
        except OSError as exc:
            raise CloseoutPlanReceiptError(
                f"closeout input disappeared after it was read: {relative}: {exc}"
            ) from exc
        if (
            _stat_identity(before) != _stat_identity(after)
            or (after.st_dev, after.st_ino) != (named_after.st_dev, named_after.st_ino)
            or link_before != link_after
        ):
            raise CloseoutPlanReceiptError(
                f"closeout input changed while it was read: {relative}"
            )
        snapshot[relative] = {
            "state": "present",
            "path": link_after,
            "byte_length": len(content),
            "sha256": hashlib.sha256(content).hexdigest(),
            "stat_guard": _stat_identity(after),
        }
    return snapshot


def _compiled_snapshot(
    root: Path,
    paths: Iterable[Path],
    *,
    reusable: Mapping[str, object] | None = None,
) -> dict[str, dict[str, Any]]:
    """Bind exact compiled bytes, using stat guards only as read accelerators."""

    snapshot: dict[str, dict[str, Any]] = {}
    logical_paths = {_logical_absolute(root, candidate) for candidate in paths}
    reusable = reusable or {}
    for path in sorted(logical_paths, key=str):
        relative = _repository_relative(root, path)
        link_before = _logical_path_projection(root, path)
        prior = reusable.get(relative)
        try:
            current_stat = path.stat()
        except FileNotFoundError:
            link_after = _logical_path_projection(root, path)
            if link_after != link_before:
                raise CloseoutPlanReceiptError(
                    f"compiled closeout input changed while inspected: {relative}"
                )
            snapshot[relative] = {
                "state": "missing",
                "path": link_after,
                "byte_length": None,
                "sha256": None,
                "stat_guard": None,
            }
            continue
        except OSError as exc:
            raise CloseoutPlanReceiptError(
                f"could not inspect compiled closeout input {relative}: {exc}"
            ) from exc
        current_guard = _stat_identity(current_stat)
        if (
            isinstance(prior, Mapping)
            and prior.get("state") == "present"
            and prior.get("path") == link_before
            and prior.get("stat_guard") == current_guard
            and isinstance(prior.get("byte_length"), int)
            and SHA256_RE.fullmatch(str(prior.get("sha256") or ""))
        ):
            snapshot[relative] = dict(prior)
            continue

        try:
            with path.open("rb") as stream:
                before = os.fstat(stream.fileno())
                content = stream.read()
                after = os.fstat(stream.fileno())
        except OSError as exc:
            raise CloseoutPlanReceiptError(
                f"could not read compiled closeout input {relative}: {exc}"
            ) from exc
        link_after = _logical_path_projection(root, path)
        try:
            named_after = path.stat()
        except OSError as exc:
            raise CloseoutPlanReceiptError(
                f"compiled closeout input disappeared after read: {relative}: {exc}"
            ) from exc
        if (
            _stat_identity(before) != _stat_identity(after)
            or (after.st_dev, after.st_ino) != (named_after.st_dev, named_after.st_ino)
            or link_before != link_after
        ):
            raise CloseoutPlanReceiptError(
                f"compiled closeout input changed while read: {relative}"
            )
        snapshot[relative] = {
            "state": "present",
            "path": link_after,
            "byte_length": len(content),
            "sha256": hashlib.sha256(content).hexdigest(),
            "stat_guard": _stat_identity(after),
        }
    return snapshot


def compiled_input_snapshot(
    root: Path,
    paths: Iterable[Path],
    *,
    reusable: Mapping[str, object] | None = None,
) -> dict[str, dict[str, Any]]:
    """Public race-safe compiled-input capture for planner advisory reuse."""

    return _compiled_snapshot(root.resolve(), paths, reusable=reusable)


def _snapshot_paths_from_ledger(
    root: Path,
    ledger: Mapping[str, object],
) -> set[Path]:
    paths: set[Path] = set()
    for raw_path in ledger:
        path = Path(str(raw_path))
        if not path.is_absolute():
            path = root / path
        logical = _logical_absolute(root, path)
        _repository_relative(root, logical)
        _resolved_repository_relative(root, logical)
        paths.add(logical)
    return paths


def _routing_projection(
    root: Path,
    entry_module: str,
    loader: Callable[[Path, str], tuple[object | None, str]] | None,
) -> object:
    if loader is None:
        try:
            from scripts.lean_import_closure import lake_routing_projection
        except ModuleNotFoundError:  # Direct ``python scripts/...`` execution.
            from lean_import_closure import lake_routing_projection

        loader = lake_routing_projection
    projection, error = loader(root, entry_module)
    if projection is None:
        raise CloseoutPlanReceiptError(
            error or "target Lake routing projection is unavailable"
        )
    return projection


def _default_external_artifact_stat_projection(
    root: Path, modules: tuple[str, ...]
) -> tuple[object | None, str]:
    """Retain cheap, path-neutral guards for exact external artifacts."""

    try:
        from scripts.lean_import_closure import (
            external_module_artifact_search_roots,
        )
    except ModuleNotFoundError:  # Direct ``python scripts/...`` execution.
        from lean_import_closure import external_module_artifact_search_roots

    search_roots, root_error = external_module_artifact_search_roots(root)
    if search_roots is None:
        return None, root_error

    module_records: list[dict[str, Any]] = []
    for module in modules:
        relative = Path(*module.split(".")).with_suffix(".olean")
        candidates: list[dict[str, Any]] = []
        selected = False
        for root_role, search_root in search_roots:
            candidate = search_root / relative
            try:
                link_stat = candidate.lstat()
                target_stat = candidate.stat()
            except FileNotFoundError:
                candidates.append({"root_role": root_role, "state": "missing"})
                continue
            except OSError as exc:
                return None, f"could not stat external Lean artifact {candidate}: {exc}"
            record: dict[str, Any] = {
                "root_role": root_role,
                "state": "present",
                "target_stat": _stat_identity(target_stat),
                "path_kind": (
                    "symlink" if stat_module.S_ISLNK(link_stat.st_mode) else "file"
                ),
            }
            candidates.append(record)
            selected = True
            break
        if not selected:
            return None, f"loaded external module has no resolvable .olean: {module}"
        module_records.append({"module": module, "candidates": candidates})
    return {
        "schema": 2,
        "search_root_roles": [role for role, _path in search_roots],
        "modules": module_records,
    }, ""


def _without_stat_guards(value: object) -> object:
    """Drop filesystem accelerators while retaining paths and exact identities."""

    if isinstance(value, Mapping):
        return {
            str(key): _without_stat_guards(item)
            for key, item in value.items()
            if key not in {"target_stat", "stat_guard"}
        }
    if isinstance(value, list):
        return [_without_stat_guards(item) for item in value]
    return value


def _plan_identity_material(value: Mapping[str, object]) -> dict[str, Any]:
    material = {
        str(key): item
        for key, item in value.items()
        if key not in {"plan_identity_sha256", "receipt_integrity_sha256"}
    }
    material["content_inputs"] = _without_stat_guards(material.get("content_inputs"))
    material["compiled_inputs"] = _without_stat_guards(
        material.get("compiled_inputs")
    )
    # New receipts bind the portable Lean closure identity separately.  The
    # large content-store object retains machine-local mutation accelerators,
    # so its reference must not enter the stable plan identity.  Historical
    # receipts lack the portable field and continue to verify under their
    # original identity rule.
    if "lean_import_closure_identity_sha256" in material:
        material.pop("lean_import_closure_projection", None)
    raw_projection = material.get("lean_import_closure_projection")
    if isinstance(raw_projection, Mapping) and "external_artifact_stats" in raw_projection:
        projection = dict(raw_projection)
        projection["external_artifact_stats"] = _without_stat_guards(
            projection.get("external_artifact_stats")
        )
        material["lean_import_closure_projection"] = projection
    return material


def _default_external_artifact_content_identity(
    root: Path, modules: tuple[str, ...]
) -> tuple[str | None, str]:
    try:
        from scripts.lean_import_closure import (
            external_module_artifact_records,
            external_module_artifacts_sha256,
        )
    except ModuleNotFoundError:  # Direct ``python scripts/...`` execution.
        from lean_import_closure import (
            external_module_artifact_records,
            external_module_artifacts_sha256,
        )

    records, error = external_module_artifact_records(
        root, modules, timeout_seconds=60
    )
    if records is None:
        return None, error
    return external_module_artifacts_sha256(records), ""


def build_lean_closure_operational_projection(
    root: Path,
    payload: object,
    *,
    external_projection_loader: (
        Callable[[Path, tuple[str, ...]], tuple[object | None, str]] | None
    ) = None,
    verify_source_content: bool = True,
) -> dict[str, Any]:
    """Validate one Lean-authored graph and bind its local operational envelope."""

    try:
        from scripts.lean_import_closure import (
            durable_lean_build_control_records,
            repository_module_ownership_snapshot,
            validated_lean_import_closure_payload,
        )
    except ModuleNotFoundError:  # Direct ``python scripts/...`` execution.
        from lean_import_closure import (
            durable_lean_build_control_records,
            repository_module_ownership_snapshot,
            validated_lean_import_closure_payload,
        )

    try:
        validated = validated_lean_import_closure_payload(payload)
    except ValueError as exc:
        raise CloseoutPlanReceiptError(
            f"Lean import-closure receipt is invalid: {exc}"
        ) from exc
    try:
        ownership_snapshot = repository_module_ownership_snapshot(root)
    except ValueError as exc:
        raise CloseoutPlanReceiptError(str(exc)) from exc
    raw_sources = validated["sources"]
    assert isinstance(raw_sources, list)
    for raw in raw_sources:
        assert isinstance(raw, Mapping)
        module = str(raw["module"])
        path = (root / str(raw["path"])).resolve()
        if ownership_snapshot.candidates(module) != (path,):
            raise CloseoutPlanReceiptError(
                f"Lean import-closure source ownership changed: {module}"
            )
        if verify_source_content:
            try:
                content = path.read_bytes()
            except OSError as exc:
                raise CloseoutPlanReceiptError(
                    f"Lean import-closure source is unavailable: {path}: {exc}"
                ) from exc
            if (
                len(content) != raw["byte_length"]
                or hashlib.sha256(content).hexdigest() != raw["sha256"]
            ):
                raise CloseoutPlanReceiptError(
                    f"Lean import-closure source bytes changed: {raw['path']}"
                )

    raw_controls = durable_lean_build_control_records(validated["build_controls"])
    assert isinstance(raw_controls, list)
    for raw in raw_controls:
        assert isinstance(raw, Mapping)
        path = root / str(raw["path"])
        try:
            content = path.read_bytes()
        except OSError as exc:
            raise CloseoutPlanReceiptError(
                f"Lean import-closure build control is unavailable: {path}: {exc}"
            ) from exc
        if (
            len(content) != raw["byte_length"]
            or hashlib.sha256(content).hexdigest() != raw["sha256"]
        ):
            raise CloseoutPlanReceiptError(
                f"Lean import-closure build control changed: {raw['path']}"
            )

    raw_external = validated["external_import_modules"]
    assert isinstance(raw_external, list)
    external_modules = tuple(str(module) for module in raw_external)
    for module in external_modules:
        candidates = ownership_snapshot.candidates(module)
        if len(candidates) > 1:
            raise CloseoutPlanReceiptError(
                f"external Lean module has ambiguous repository source ownership: {module}"
            )
        if candidates:
            raise CloseoutPlanReceiptError(
                f"external Lean module gained repository source ownership: {module}"
            )
    loader = external_projection_loader or _default_external_artifact_stat_projection
    external_projection, error = loader(root, external_modules)
    if external_projection is None:
        raise CloseoutPlanReceiptError(
            error or "external Lean artifact projection is unavailable"
        )
    return {
        "schema": LEAN_CLOSURE_OPERATIONAL_PROJECTION_SCHEMA,
        "state": "present",
        "lean_import_closure": validated,
        "external_artifact_stats": external_projection,
    }


def validate_lean_closure_operational_projection(
    root: Path,
    recorded: object,
    *,
    external_projection_loader: (
        Callable[[Path, tuple[str, ...]], tuple[object | None, str]] | None
    ) = None,
    external_content_identity_loader: (
        Callable[[Path, tuple[str, ...]], tuple[str | None, str]] | None
    ) = None,
) -> dict[str, Any]:
    """Revalidate graph membership, ownership, source bytes, and artifact guards."""

    if recorded == {"state": "not_bound"}:
        return {"state": "not_bound"}
    if (
        not isinstance(recorded, Mapping)
        or recorded.get("schema") != LEAN_CLOSURE_OPERATIONAL_PROJECTION_SCHEMA
        or recorded.get("state") != "present"
        or set(recorded)
        != {"schema", "state", "lean_import_closure", "external_artifact_stats"}
    ):
        raise CloseoutPlanReceiptError(
            "Lean import-closure operational projection is malformed"
        )
    current = build_lean_closure_operational_projection(
        root,
        recorded.get("lean_import_closure"),
        external_projection_loader=external_projection_loader,
        verify_source_content=False,
    )
    expected = {str(key): value for key, value in recorded.items()}
    if current != expected:
        raw_closure = current.get("lean_import_closure")
        raw_modules = (
            raw_closure.get("external_import_modules")
            if isinstance(raw_closure, Mapping)
            else None
        )
        expected_digest = (
            str(raw_closure.get("external_module_artifacts_sha256") or "")
            if isinstance(raw_closure, Mapping)
            else ""
        )
        if not isinstance(raw_modules, list):
            raise CloseoutPlanReceiptError(
                "Lean import-closure external artifact identity is malformed"
            )
        loader = (
            external_content_identity_loader
            or _default_external_artifact_content_identity
        )
        current_digest, error = loader(
            root, tuple(str(module) for module in raw_modules)
        )
        if current_digest != expected_digest:
            raise CloseoutPlanReceiptError(
                error or "Lean import-closure external artifact bytes changed"
            )
    return current


def target_audit_config_projection(root: Path, paper: str) -> dict[str, Any]:
    """Project shared audit configuration onto one selected paper.

    Other papers' membership and configuration must not reopen this paper. The
    projection deliberately retains only schema plus membership in paper lists
    and exact entries from paper-keyed mappings.
    """

    path = root / "papers" / "audit_config.json"
    try:
        payload = json.loads(path.read_text(encoding="utf-8"))
    except FileNotFoundError:
        return {"state": "missing"}
    except (OSError, json.JSONDecodeError) as exc:
        raise CloseoutPlanReceiptError(
            f"could not project target audit configuration: {exc}"
        ) from exc
    if not isinstance(payload, Mapping):
        raise CloseoutPlanReceiptError("audit configuration is not an object")
    projection: dict[str, Any] = {
        "state": "present",
        "schema": payload.get("schema"),
    }
    for raw_key, raw_value in payload.items():
        key = str(raw_key)
        if key in {"schema", "description", "generic_source_hygiene_allowed_terms"}:
            continue
        if isinstance(raw_value, list) and key.endswith("_papers"):
            projection[key] = paper in {
                str(value).strip() for value in raw_value if str(value).strip()
            }
        elif isinstance(raw_value, Mapping) and paper in raw_value:
            projection[key] = raw_value[paper]
        elif isinstance(raw_value, Mapping):
            if not raw_value or not all(
                PAPER_ID_RE.fullmatch(str(candidate)) for candidate in raw_value
            ):
                projection[key] = raw_value
        elif not isinstance(raw_value, Mapping):
            projection[key] = raw_value
    return projection


def target_aggregate_status_projection(root: Path, paper: str) -> dict[str, Any]:
    """Return only this paper's entry from the generated aggregate status."""

    path = root / "papers" / "status.json"
    try:
        payload = json.loads(path.read_text(encoding="utf-8"))
    except FileNotFoundError:
        return {"state": "missing"}
    except (OSError, json.JSONDecodeError) as exc:
        raise CloseoutPlanReceiptError(
            f"could not project target aggregate status: {exc}"
        ) from exc
    raw_papers = payload.get("papers") if isinstance(payload, Mapping) else None
    if not isinstance(raw_papers, list):
        raise CloseoutPlanReceiptError("aggregate paper status has no papers list")
    matches = [
        dict(item)
        for item in raw_papers
        if isinstance(item, Mapping) and item.get("id") == paper
    ]
    if len(matches) != 1:
        return {"state": "missing_or_ambiguous", "matches": len(matches)}
    return {"state": "present", "entry": matches[0]}


def strict_closeout_protocol_projection(root: Path) -> dict[str, Any]:
    """Return the versioned semantic compatibility authority for closeout.

    A correctness change that invalidates prior strict results must bump this
    protocol identity or one of its projected audit versions. Ordinary
    operational implementation edits deliberately do not reopen papers.
    """

    path = root / "config" / "formalization_audit_protocol.json"
    try:
        payload = json.loads(path.read_text(encoding="utf-8"))
    except FileNotFoundError:
        return {"state": "missing"}
    except (OSError, json.JSONDecodeError) as exc:
        raise CloseoutPlanReceiptError(
            f"could not read formalization audit protocol: {exc}"
        ) from exc
    try:
        from scripts.formalization_protocol import (
            formalization_review_protocol_digest,
        )
    except ModuleNotFoundError:  # Direct ``python scripts/...`` execution.
        from formalization_protocol import formalization_review_protocol_digest

    try:
        digest = formalization_review_protocol_digest(payload)
    except (TypeError, ValueError) as exc:
        raise CloseoutPlanReceiptError(
            f"formalization audit protocol is invalid: {exc}"
        ) from exc
    return {
        "state": "present",
        "formalization_review_protocol_sha256": digest,
    }


def target_lean_file_inventory(root: Path, paper: str) -> list[str]:
    """Return the exact paper-local Lean file set selected by strict closeout."""

    folder = root / "papers" / paper
    files = [path for path in folder.rglob("*.lean") if path.is_file()]
    aggregator = root / "papers" / f"{paper}.lean"
    if aggregator.is_file():
        files.append(aggregator)
    return sorted({_repository_relative(root, path) for path in files})


def content_input_snapshot(
    root: Path,
    paths: Iterable[Path],
    *,
    reusable: Mapping[str, object] | None = None,
) -> dict[str, dict[str, Any]]:
    """Public logical-path content snapshot used by the advisory cache."""

    return _content_snapshot(root.resolve(), paths, reusable=reusable)


def validate_content_input_snapshot(
    root: Path, recorded: object
) -> tuple[dict[str, dict[str, Any]] | None, str]:
    """Revalidate one recorded logical-path snapshot without semantic authority."""

    if not isinstance(recorded, Mapping):
        return None, "recorded closeout content snapshot is malformed"
    try:
        current = _content_snapshot(
            root.resolve(),
            (root / str(relative) for relative in recorded),
            reusable=recorded,
        )
    except CloseoutPlanReceiptError as exc:
        return None, str(exc)
    expected = {
        str(relative): dict(value) if isinstance(value, Mapping) else value
        for relative, value in recorded.items()
    }
    if _without_stat_guards(current) != _without_stat_guards(expected):
        return None, "recorded closeout content inputs changed"
    return current, ""


def build_closeout_plan_receipt(
    root: Path,
    *,
    paper: str,
    deep_paper_prose: bool,
    content_paths: Iterable[Path],
    stat_paths: Iterable[Path],
    source_ledger: Mapping[str, object],
    compiled_ledger: Mapping[str, object],
    lean_import_closure_projection: object | None = None,
    lean_import_closure_projection_validated: bool = False,
    v11_lean_review_graph: Mapping[str, object] | None = None,
    final_holistic_audit_surface: Mapping[str, object] | None = None,
    all_selected_semantic_review_sha256: str = "",
    reusable_content_inputs: Mapping[str, object] | None = None,
    reusable_compiled_inputs: Mapping[str, object] | None = None,
    routing_projection_loader: (
        Callable[[Path, str], tuple[object | None, str]] | None
    ) = None,
    external_projection_loader: (
        Callable[[Path, tuple[str, ...]], tuple[object | None, str]] | None
    ) = None,
) -> dict[str, Any]:
    """Capture one immutable target-scoped snapshot and its launch identity."""

    root = root.resolve()
    entry_module = paper
    content_path_set = {
        _logical_absolute(root, candidate) for candidate in content_paths
    }
    content_path_set.update(_snapshot_paths_from_ledger(root, source_ledger))
    lean_inventory = target_lean_file_inventory(root, paper)
    content_path_set.update(root / relative for relative in lean_inventory)
    stat_path_set = {_logical_absolute(root, candidate) for candidate in stat_paths}
    stat_path_set.update(_snapshot_paths_from_ledger(root, compiled_ledger))
    if lean_import_closure_projection is None:
        closure_projection = {"state": "not_bound"}
    elif lean_import_closure_projection_validated:
        if (
            not isinstance(lean_import_closure_projection, Mapping)
            or lean_import_closure_projection.get("state") != "present"
        ):
            raise CloseoutPlanReceiptError(
                "prevalidated Lean import-closure projection is unavailable"
            )
        closure_projection = dict(lean_import_closure_projection)
    else:
        closure_projection = validate_lean_closure_operational_projection(
            root,
            lean_import_closure_projection,
            external_projection_loader=external_projection_loader,
        )
    raw_closure = closure_projection.get("lean_import_closure")
    if isinstance(raw_closure, Mapping):
        if (
            raw_closure.get("entry_module") != paper
            or raw_closure.get("entrypoint") != f"papers/{paper}.lean"
        ):
            raise CloseoutPlanReceiptError(
                "Lean import-closure receipt is not rooted at the selected paper target"
            )
        raw_sources = raw_closure.get("sources")
        if isinstance(raw_sources, list):
            content_path_set.update(
                root / str(raw["path"])
                for raw in raw_sources
                if isinstance(raw, Mapping) and isinstance(raw.get("path"), str)
            )
        try:
            from scripts.lean_import_closure import durable_lean_build_control_records
        except ModuleNotFoundError:  # Direct ``python scripts/...`` execution.
            from lean_import_closure import durable_lean_build_control_records

        raw_controls = durable_lean_build_control_records(
            raw_closure.get("build_controls")
        )
        if isinstance(raw_controls, list):
            content_path_set.update(
                root / str(raw["path"])
                for raw in raw_controls
                if isinstance(raw, Mapping) and isinstance(raw.get("path"), str)
            )
    # ``status.json`` mixes acceptance-relevant configuration with generated
    # PaperInterface display metadata and optional human-review annotations.
    # Bind the conservative typed projection below instead of the whole
    # container so those non-authoritative fields cannot invalidate a plan.
    status_path = root / "papers" / paper / "status.json"
    content_path_set.discard(_logical_absolute(root, status_path))
    try:
        status_projection = paper_status_acceptance_projection(root, paper)
    except CloseoutStatusProjectionError as exc:
        raise CloseoutPlanReceiptError(str(exc)) from exc
    closure_reference = store_closeout_object(
        root,
        _without_stat_guards(closure_projection),
        kind="lean_import_closure_projection",
    )
    try:
        closure_identity_sha256 = portable_evidence_sha256(
            portable_lean_closure_identity(closure_projection)
        )
    except PortableEvidenceIdentityError as exc:
        raise CloseoutPlanReceiptError(
            f"Lean import-closure portable identity is unavailable: {exc}"
        ) from exc
    graph_reference = (
        store_closeout_object(
            root,
            v11_lean_review_graph,
            kind="v11_lean_review_graph",
        )
        if v11_lean_review_graph is not None
        else None
    )
    if final_holistic_audit_surface is not None:
        if (
            not final_holistic_audit_surface_contract_is_supported(
                final_holistic_audit_surface
            )
            or final_holistic_audit_surface.get("paper") != paper
        ):
            raise CloseoutPlanReceiptError(
                "final holistic audit surface is malformed or belongs to another paper"
            )
        final_surface = dict(final_holistic_audit_surface)
        final_surface_sha256 = final_holistic_audit_surface_sha256(final_surface)
        final_surface_reference = store_closeout_object(
            root,
            final_surface,
            kind="final_holistic_audit_surface",
        )
    else:
        final_surface_sha256 = ""
        final_surface_reference = None
    semantic_review_sha256 = str(all_selected_semantic_review_sha256).strip().lower()
    if graph_reference is not None:
        if not SHA256_RE.fullmatch(semantic_review_sha256):
            raise CloseoutPlanReceiptError(
                "v11 closeout plan lacks its all-selected semantic-review identity"
            )
    elif semantic_review_sha256:
        raise CloseoutPlanReceiptError(
            "all-selected semantic-review identity cannot be bound without a v11 Lean graph"
        )
    material = {
        "schema": CLOSEOUT_PLAN_RECEIPT_SCHEMA,
        "acceptance_credential": False,
        "operational_scheduling_only": True,
        "plan_identity_schema": OPERATIONAL_PLAN_IDENTITY_SCHEMA,
        "paper": paper,
        "deep_paper_prose": deep_paper_prose,
        "entry_module": entry_module,
        "content_inputs": _content_snapshot(
            root, content_path_set, reusable=reusable_content_inputs
        ),
        "compiled_inputs": _compiled_snapshot(
            root, stat_path_set, reusable=reusable_compiled_inputs
        ),
        "target_lean_file_inventory": lean_inventory,
        "target_paper_status_projection": status_projection,
        "lean_import_closure_projection": closure_reference,
        "lean_import_closure_identity_sha256": closure_identity_sha256,
        "v11_lean_review_graph": graph_reference,
        "final_holistic_audit_surface": final_surface_reference,
        "final_holistic_audit_surface_sha256": final_surface_sha256,
        "all_selected_semantic_review_sha256": semantic_review_sha256,
        "target_audit_config_projection": target_audit_config_projection(root, paper),
        "strict_closeout_protocol_projection": strict_closeout_protocol_projection(
            root
        ),
        "lake_routing_projection_sha256": _stable_digest(
            _routing_projection(root, entry_module, routing_projection_loader)
        ),
    }
    material["plan_identity_sha256"] = _stable_digest(
        _plan_identity_material(material)
    )
    material["receipt_integrity_sha256"] = _stable_digest(material)
    return material


def validated_closeout_plan_receipt(
    root: Path,
    value: object,
    *,
    paper: str,
    deep_paper_prose: bool,
    expected_plan_identity: str,
    routing_projection_loader: (
        Callable[[Path, str], tuple[object | None, str]] | None
    ) = None,
    external_projection_loader: (
        Callable[[Path, tuple[str, ...]], tuple[object | None, str]] | None
    ) = None,
    external_content_identity_loader: (
        Callable[[Path, tuple[str, ...]], tuple[str | None, str]] | None
    ) = None,
) -> dict[str, Any]:
    """Validate structure, identity, and every current target input."""

    if not isinstance(value, Mapping):
        raise CloseoutPlanReceiptError("closeout plan receipt is not an object")
    receipt = dict(value)
    required = {
        "schema",
        "acceptance_credential",
        "operational_scheduling_only",
        "plan_identity_schema",
        "plan_identity_sha256",
        "receipt_integrity_sha256",
        "paper",
        "deep_paper_prose",
        "entry_module",
        "content_inputs",
        "compiled_inputs",
        "target_lean_file_inventory",
        "lean_import_closure_projection",
        "target_audit_config_projection",
        "strict_closeout_protocol_projection",
        "lake_routing_projection_sha256",
    }
    portable_required = required | {"lean_import_closure_identity_sha256"}
    schema4_required = portable_required | {"target_paper_status_projection"}
    schema5_required = schema4_required | {"v11_lean_review_graph"}
    current_required = schema5_required | {
        "final_holistic_audit_surface",
        "final_holistic_audit_surface_sha256",
    }
    schema7_required = current_required | {
        "all_selected_semantic_review_sha256",
    }
    schema = receipt.get("schema")
    if schema == CLOSEOUT_PLAN_RECEIPT_SCHEMA:
        expected_fields = {frozenset(schema7_required)}
    elif schema == 6:
        expected_fields = {frozenset(current_required)}
    elif schema == 5:
        expected_fields = {frozenset(schema5_required)}
    elif schema == 4:
        expected_fields = {frozenset(schema4_required)}
    else:
        expected_fields = {frozenset(required), frozenset(portable_required)}
    if set(receipt) not in expected_fields:
        raise CloseoutPlanReceiptError("closeout plan receipt fields are malformed")
    expected_identity_schema = {
        CLOSEOUT_PLAN_RECEIPT_SCHEMA: OPERATIONAL_PLAN_IDENTITY_SCHEMA,
        6: PREVIOUS_OPERATIONAL_PLAN_IDENTITY_SCHEMA,
        5: SCHEMA5_OPERATIONAL_PLAN_IDENTITY_SCHEMA,
        4: SCHEMA4_OPERATIONAL_PLAN_IDENTITY_SCHEMA,
    }.get(schema, LEGACY_OPERATIONAL_PLAN_IDENTITY_SCHEMA)
    if (
        schema not in SUPPORTED_CLOSEOUT_PLAN_RECEIPT_SCHEMAS
        or receipt.get("acceptance_credential") is not False
        or receipt.get("operational_scheduling_only") is not True
        or receipt.get("plan_identity_schema") != expected_identity_schema
        or receipt.get("paper") != paper
        or receipt.get("entry_module") != paper
        or receipt.get("deep_paper_prose") is not deep_paper_prose
        or not SHA256_RE.fullmatch(str(receipt.get("plan_identity_sha256") or ""))
        or not SHA256_RE.fullmatch(
            str(receipt.get("receipt_integrity_sha256") or "")
        )
        or not SHA256_RE.fullmatch(expected_plan_identity)
        or receipt.get("plan_identity_sha256") != expected_plan_identity
    ):
        raise CloseoutPlanReceiptError(
            "closeout plan receipt does not match the requested paper/profile/identity"
        )
    integrity_material = dict(receipt)
    recorded_integrity = str(integrity_material.pop("receipt_integrity_sha256"))
    if _stable_digest(integrity_material) != recorded_integrity:
        raise CloseoutPlanReceiptError("closeout plan receipt integrity is corrupt")
    recorded_identity = str(receipt["plan_identity_sha256"])
    if _stable_digest(_plan_identity_material(receipt)) != recorded_identity:
        raise CloseoutPlanReceiptError("closeout plan receipt identity is corrupt")

    raw_content = receipt.get("content_inputs")
    raw_compiled = receipt.get("compiled_inputs")
    if not isinstance(raw_content, Mapping) or not isinstance(raw_compiled, Mapping):
        raise CloseoutPlanReceiptError("closeout plan input snapshots are malformed")
    if schema in {4, 5, 6, CLOSEOUT_PLAN_RECEIPT_SCHEMA}:
        status_relative = f"papers/{paper}/status.json"
        if status_relative in raw_content:
            raise CloseoutPlanReceiptError(
                "derived paper status container must not enter the current content snapshot"
            )
        try:
            current_status_projection = paper_status_acceptance_projection(root, paper)
        except CloseoutStatusProjectionError as exc:
            raise CloseoutPlanReceiptError(str(exc)) from exc
        if current_status_projection != receipt.get("target_paper_status_projection"):
            raise CloseoutPlanReceiptError(
                "paper status acceptance configuration changed; run the planner again"
            )
    current_content, content_error = validate_content_input_snapshot(root, raw_content)
    if current_content is None:
        raise CloseoutPlanReceiptError(f"{content_error}; run the planner again")
    current_compiled = _compiled_snapshot(
        root,
        (root / str(relative) for relative in raw_compiled),
        reusable=raw_compiled,
    )
    if _without_stat_guards(current_compiled) != _without_stat_guards(raw_compiled):
        raise CloseoutPlanReceiptError(
            "closeout Lean/source/compiled inputs changed; run the planner again"
        )
    if target_lean_file_inventory(root, paper) != receipt.get(
        "target_lean_file_inventory"
    ):
        raise CloseoutPlanReceiptError(
            "target paper Lean-file inventory changed; run the planner again"
        )
    if target_audit_config_projection(root, paper) != receipt.get(
        "target_audit_config_projection"
    ):
        raise CloseoutPlanReceiptError(
            "target audit configuration changed; run the planner again"
        )
    resolved_closure_projection = resolved_plan_lean_closure_projection(root, receipt)
    recorded_closure_identity = receipt.get("lean_import_closure_identity_sha256")
    if recorded_closure_identity is not None:
        try:
            current_closure_identity = portable_evidence_sha256(
                portable_lean_closure_identity(resolved_closure_projection)
            )
        except PortableEvidenceIdentityError as exc:
            raise CloseoutPlanReceiptError(
                f"Lean import-closure portable identity is invalid: {exc}"
            ) from exc
        if (
            not SHA256_RE.fullmatch(str(recorded_closure_identity))
            or recorded_closure_identity != current_closure_identity
        ):
            raise CloseoutPlanReceiptError(
                "Lean import-closure portable identity does not match its object"
            )
    validate_lean_closure_operational_projection(
        root,
        resolved_closure_projection,
        external_projection_loader=external_projection_loader,
        external_content_identity_loader=external_content_identity_loader,
    )
    if schema in {5, 6, CLOSEOUT_PLAN_RECEIPT_SCHEMA}:
        resolved_plan_v11_lean_review_graph(root, receipt)
    if schema in {6, CLOSEOUT_PLAN_RECEIPT_SCHEMA}:
        stored_surface = resolved_plan_final_holistic_audit_surface(root, receipt)
        graph = resolved_plan_v11_lean_review_graph(root, receipt)
        recorded_surface_sha256 = str(
            receipt.get("final_holistic_audit_surface_sha256") or ""
        ).strip().lower()
        if graph is None:
            if stored_surface is not None or recorded_surface_sha256:
                raise CloseoutPlanReceiptError(
                    "final holistic audit surface cannot be bound without a v11 Lean graph"
                )
        else:
            if stored_surface is None or not SHA256_RE.fullmatch(
                recorded_surface_sha256
            ):
                raise CloseoutPlanReceiptError(
                    "v11 closeout plan lacks its final holistic audit surface"
                )
            try:
                current_surface = build_final_holistic_audit_surface_from_repository(
                    root,
                    paper=paper,
                    graph=graph,
                    status_projection=receipt["target_paper_status_projection"],
                )
            except FinalHolisticAuditSurfaceError as exc:
                raise CloseoutPlanReceiptError(str(exc)) from exc
            if (
                current_surface != stored_surface
                or final_holistic_audit_surface_sha256(current_surface)
                != recorded_surface_sha256
            ):
                raise CloseoutPlanReceiptError(
                    "final holistic audit surface changed; run the planner again"
                )
        if schema == CLOSEOUT_PLAN_RECEIPT_SCHEMA:
            semantic_review_sha256 = str(
                receipt.get("all_selected_semantic_review_sha256") or ""
            ).strip().lower()
            if graph is None:
                if semantic_review_sha256:
                    raise CloseoutPlanReceiptError(
                        "all-selected semantic-review identity cannot be bound without "
                        "a v11 Lean graph"
                    )
            elif not SHA256_RE.fullmatch(semantic_review_sha256):
                raise CloseoutPlanReceiptError(
                    "v11 closeout plan lacks its all-selected semantic-review identity"
                )
    if strict_closeout_protocol_projection(root) != receipt.get(
        "strict_closeout_protocol_projection"
    ):
        raise CloseoutPlanReceiptError(
            "strict closeout protocol compatibility changed; run the planner again"
        )
    current_routing_sha256 = _stable_digest(
        _routing_projection(root, paper, routing_projection_loader)
    )
    if current_routing_sha256 != receipt.get("lake_routing_projection_sha256"):
        raise CloseoutPlanReceiptError(
            "target Lake routing changed; run the planner again"
        )
    return receipt


def load_validated_closeout_plan_receipt(
    root: Path,
    *,
    paper: str,
    deep_paper_prose: bool,
    expected_plan_identity: str,
) -> tuple[dict[str, Any] | None, str]:
    path = closeout_plan_receipt_path(root, paper, expected_plan_identity)
    try:
        payload = json.loads(path.read_text(encoding="utf-8"))
    except FileNotFoundError:
        return None, f"closeout plan receipt is missing: {path}"
    except (OSError, json.JSONDecodeError) as exc:
        return None, f"could not read closeout plan receipt: {exc}"
    try:
        return (
            validated_closeout_plan_receipt(
                root,
                payload,
                paper=paper,
                deep_paper_prose=deep_paper_prose,
                expected_plan_identity=expected_plan_identity,
            ),
            "",
        )
    except CloseoutPlanReceiptError as exc:
        return None, str(exc)
