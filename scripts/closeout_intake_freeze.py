#!/usr/bin/env python3
"""Fail-closed current and historical source-intake validation.

Current papers use one reviewed source-inventory plan. Papers whose tracked
status predates that consolidation may retain the exact source-atom intake seal
or the one-time trusted-rollout comparison. This module can reject a closeout
route but cannot select semantic claims, invoke Lean, schedule work, issue
evidence, or accept a paper.
"""

from __future__ import annotations

from functools import lru_cache
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import sys
import tempfile
from typing import Any, Mapping

ROOT = Path(__file__).resolve().parents[1]
if __package__ in {None, ""}:
    repository_root = str(ROOT)
    if repository_root not in sys.path:
        sys.path.insert(0, repository_root)

from scripts.closeout_plan_receipt import (
    CloseoutPlanReceiptError,
    resolved_plan_lean_closure_projection,
    strict_closeout_protocol_projection,
    target_audit_config_projection,
)
from scripts.lean_import_closure import (
    lake_routing_projection,
    validated_lean_import_closure_payload,
)
from scripts.source_map_inventory import inventory_from_source_map
from scripts.source_artifact_companion import (
    semantic_review_source_identity,
    source_text_companion_validation_issues,
)


SHA256_RE = re.compile(r"^[0-9a-f]{64}$")
INTAKE_SOURCE_IDENTITY = "source-location+normalized-statement-sha256-v1"
INTAKE_FREEZE_LEGACY_BASELINE_COMMIT = "2b500d8689a74616210a675192d14d83ac192c9f"
SOURCE_INVENTORY_REVIEW_REQUIRED_FIELD = "source_inventory_review_required"
SOURCE_INVENTORY_REVIEW_CONFIG = "v11_source_map_preparation_config.json"


def _digest(value: object) -> str:
    return hashlib.sha256(
        json.dumps(
            value,
            ensure_ascii=True,
            sort_keys=True,
            separators=(",", ":"),
            default=str,
        ).encode("utf-8")
    ).hexdigest()


@lru_cache(maxsize=None)
def _paper_predates_intake_freeze_baseline(root: str, paper: str) -> bool:
    """Use one immutable rollout tree, never a mutable status marker, as legacy authority."""

    try:
        result = subprocess.run(
            [
                "git",
                "cat-file",
                "-e",
                f"{INTAKE_FREEZE_LEGACY_BASELINE_COMMIT}:papers/{paper}/status.json",
            ],
            cwd=root,
            stdout=subprocess.DEVNULL,
            stderr=subprocess.DEVNULL,
            check=False,
        )
    except OSError:
        return False
    return result.returncode == 0


def _git_blob_at_rollout(root: Path, relative: str) -> tuple[bytes | None, str]:
    try:
        result = subprocess.run(
            [
                "git",
                "show",
                f"{INTAKE_FREEZE_LEGACY_BASELINE_COMMIT}:{relative}",
            ],
            cwd=root,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            check=False,
        )
    except OSError as exc:
        return None, f"could not read trusted rollout tree: {exc}"
    if result.returncode == 0:
        return result.stdout, ""
    return None, ""


def _git_mode_at_rollout(root: Path, relative: str) -> tuple[str | None, str]:
    try:
        result = subprocess.run(
            [
                "git",
                "ls-tree",
                INTAKE_FREEZE_LEGACY_BASELINE_COMMIT,
                "--",
                relative,
            ],
            cwd=root,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            text=True,
            check=False,
        )
    except OSError as exc:
        return None, f"could not inspect trusted rollout tree: {exc}"
    if result.returncode != 0:
        return None, (
            "could not inspect trusted rollout tree: " + result.stderr.strip()
        )
    rows = [line for line in result.stdout.splitlines() if line.strip()]
    if not rows:
        return None, ""
    if len(rows) != 1 or "\t" not in rows[0]:
        return None, f"trusted rollout tree has an ambiguous path: {relative}"
    header, recorded_path = rows[0].split("\t", 1)
    fields = header.split()
    if recorded_path != relative or len(fields) != 3:
        return None, f"trusted rollout tree has a malformed path: {relative}"
    return fields[0], ""


def _rollout_content_input_error(
    root: Path, relative: str, identity: object
) -> str:
    """Compare one selected current content input with its rollout-tree value."""

    if not isinstance(identity, Mapping):
        return f"current content input is malformed: {relative}"
    mode, mode_error = _git_mode_at_rollout(root, relative)
    if mode_error:
        return mode_error
    state = identity.get("state")
    path_projection = identity.get("path")
    if state == "missing":
        return "" if mode is None else f"content input was present at rollout: {relative}"
    if state != "present" or not isinstance(path_projection, Mapping):
        return f"current content input is malformed: {relative}"
    logical_state = path_projection.get("logical_state")
    resolved_path = str(path_projection.get("resolved_path") or "")
    if logical_state == "regular":
        if mode not in {"100644", "100755"} or resolved_path != relative:
            return f"content input path identity differs from rollout: {relative}"
    elif logical_state == "symlink":
        link_target = path_projection.get("link_target")
        link_blob, blob_error = _git_blob_at_rollout(root, relative)
        if blob_error:
            return blob_error
        if (
            mode != "120000"
            or not isinstance(link_target, str)
            or link_blob != os.fsencode(link_target)
        ):
            return f"content input symlink differs from rollout: {relative}"
    else:
        return f"content input has unsupported path identity: {relative}"
    baseline, blob_error = _git_blob_at_rollout(root, resolved_path)
    if blob_error:
        return blob_error
    if (
        baseline is None
        or len(baseline) != identity.get("byte_length")
        or hashlib.sha256(baseline).hexdigest() != identity.get("sha256")
    ):
        return f"content input differs from rollout: {relative}"
    return ""


def _rollout_graph_errors(
    root: Path, paper: str, current_closure: object
) -> list[str]:
    """Compare current ownership with Lean's recorded rollout review graph."""

    baseline_blob, blob_error = _git_blob_at_rollout(
        root, f"papers/{paper}/audit/source_record_audit.json"
    )
    if blob_error:
        return [blob_error]
    if baseline_blob is None:
        return ["trusted rollout has no Lean-authored source-record graph"]
    try:
        baseline_payload = json.loads(baseline_blob)
        baseline = validated_lean_import_closure_payload(
            baseline_payload.get("lean_import_closure")
        )
        current = validated_lean_import_closure_payload(current_closure)
    except (AttributeError, json.JSONDecodeError, UnicodeDecodeError, ValueError) as exc:
        return [f"trusted rollout Lean graph is unavailable: {exc}"]

    current_sources = {
        str(raw["module"]): str(raw["path"])
        for raw in current["sources"]
        if isinstance(raw, Mapping)
    }
    baseline_sources = {
        str(raw["module"]): str(raw["path"])
        for raw in baseline["sources"]
        if isinstance(raw, Mapping)
    }
    expected_sources = dict(baseline_sources)
    current_entry_module = str(current["entry_module"])
    current_entrypoint = str(current["entrypoint"])
    expected_entrypoint = f"papers/{paper}.lean"
    if current_entry_module != paper or current_entrypoint != expected_entrypoint:
        errors = ["current Lean graph is not rooted at the selected paper target"]
    else:
        errors = []
    if (
        current_entry_module == paper
        and current_entrypoint == expected_entrypoint
        and current_entry_module not in expected_sources
    ):
        # The closeout receipt is rooted at papers/<Paper>.lean, while the
        # rollout source-record graph is commonly rooted at PaperInterface.
        # Permit exactly that current root wrapper, not arbitrary new imports.
        expected_sources[current_entry_module] = current_entrypoint
    current_external = {str(module) for module in current["external_import_modules"]}
    baseline_external = {
        str(module) for module in baseline["external_import_modules"]
    }
    for module in sorted(set(expected_sources) | set(current_sources)):
        if current_sources.get(module) != expected_sources.get(module):
            errors.append(
                f"Lean source ownership differs from rollout graph: {module}"
            )
    for module in sorted(baseline_external ^ current_external):
        errors.append(
            f"external Lean ownership differs from rollout graph: {module}"
        )
    expected_loaded = set(expected_sources) | baseline_external
    if expected_loaded != set(current["lean_loaded_modules"]):
        for module in sorted(
            expected_loaded ^ set(str(value) for value in current["lean_loaded_modules"])
        ):
            errors.append(
                f"Lean loaded-module membership differs from rollout graph: {module}"
            )
    return errors


def _legacy_rollout_material_readiness(
    folder: Path, receipt: Mapping[str, Any]
) -> dict[str, Any]:
    """Prove first legacy adoption still matches the trusted rollout tree.

    This guard is deterministic and tracked. The ignored adoption record may be
    deleted without allowing a paper edited after rollout to acquire a new
    baseline. Administrative workflow code is deliberately outside the check.
    """

    root = ROOT.resolve()
    paper = folder.name
    errors: list[str] = []
    raw_content_inputs = receipt.get("content_inputs")
    if not isinstance(raw_content_inputs, Mapping):
        return {
            "ready": False,
            "state": "error",
            "errors": ["current plan has no exact content-input projection"],
        }
    paper_prefix = f"papers/{paper}/"
    paper_root = f"papers/{paper}.lean"
    for raw_relative, identity in raw_content_inputs.items():
        relative = str(raw_relative)
        if relative != paper_root and not relative.startswith(paper_prefix):
            continue
        error = _rollout_content_input_error(root, relative, identity)
        if error:
            errors.append(error)

    try:
        inventory_result = subprocess.run(
            [
                "git",
                "ls-tree",
                "-r",
                "--name-only",
                INTAKE_FREEZE_LEGACY_BASELINE_COMMIT,
                "--",
                f"papers/{paper}",
                f"papers/{paper}.lean",
            ],
            cwd=root,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            text=True,
            check=False,
        )
    except OSError as exc:
        return {
            "ready": False,
            "state": "error",
            "errors": [f"could not inventory trusted rollout tree: {exc}"],
        }
    if inventory_result.returncode != 0:
        return {
            "ready": False,
            "state": "error",
            "errors": [
                "could not inventory target paper in the trusted rollout tree: "
                + inventory_result.stderr.strip()
            ],
        }
    baseline_lean_inventory = sorted(
        line.strip()
        for line in inventory_result.stdout.splitlines()
        if line.strip().endswith(".lean")
    )
    current_lean_inventory = receipt.get("target_lean_file_inventory")
    if current_lean_inventory != baseline_lean_inventory:
        errors.append("target paper Lean-file inventory differs from the rollout tree")

    try:
        raw_projection = resolved_plan_lean_closure_projection(root, receipt)
    except CloseoutPlanReceiptError as exc:
        return {
            "ready": False,
            "state": "error",
            "errors": [str(exc)],
        }
    raw_closure = (
        raw_projection.get("lean_import_closure")
        if isinstance(raw_projection, Mapping)
        else None
    )
    raw_sources = (
        raw_closure.get("sources") if isinstance(raw_closure, Mapping) else None
    )
    if not isinstance(raw_sources, list):
        return {
            "ready": False,
            "state": "error",
            "errors": ["current plan has no Lean-authored source closure"],
        }
    errors.extend(_rollout_graph_errors(root, paper, raw_closure))
    for raw in raw_sources:
        if not isinstance(raw, Mapping):
            return {
                "ready": False,
                "state": "error",
                "errors": ["current Lean source closure is malformed"],
            }
        relative = str(raw.get("path") or "")
        baseline, blob_error = _git_blob_at_rollout(root, relative)
        if blob_error:
            return {"ready": False, "state": "error", "errors": [blob_error]}
        if baseline is None or hashlib.sha256(baseline).hexdigest() != raw.get(
            "sha256"
        ):
            errors.append(f"Lean source differs from rollout: {relative}")

    raw_controls = (
        raw_closure.get("build_controls") if isinstance(raw_closure, Mapping) else None
    )
    if not isinstance(raw_controls, list):
        return {
            "ready": False,
            "state": "error",
            "errors": ["current plan has no Lean build-control closure"],
        }
    for raw in raw_controls:
        if not isinstance(raw, Mapping):
            return {
                "ready": False,
                "state": "error",
                "errors": ["current Lean build-control closure is malformed"],
            }
        relative = str(raw.get("path") or "")
        baseline, blob_error = _git_blob_at_rollout(root, relative)
        if blob_error:
            return {"ready": False, "state": "error", "errors": [blob_error]}
        if baseline is None or hashlib.sha256(baseline).hexdigest() != raw.get(
            "sha256"
        ):
            errors.append(f"Lean build control differs from rollout: {relative}")

    audit_config, audit_error = _git_blob_at_rollout(root, "papers/audit_config.json")
    protocol, protocol_error = _git_blob_at_rollout(
        root, "config/formalization_audit_protocol.json"
    )
    if audit_error or protocol_error or audit_config is None or protocol is None:
        return {
            "ready": False,
            "state": "error",
            "errors": [
                audit_error
                or protocol_error
                or "trusted rollout configuration is unavailable"
            ],
        }
    with tempfile.TemporaryDirectory() as temp_dir:
        baseline_root = Path(temp_dir)
        (baseline_root / "papers").mkdir()
        (baseline_root / "config").mkdir()
        (baseline_root / "papers" / "audit_config.json").write_bytes(audit_config)
        (baseline_root / "config" / "formalization_audit_protocol.json").write_bytes(
            protocol
        )
        try:
            baseline_target_config = target_audit_config_projection(
                baseline_root, paper
            )
            baseline_protocol = strict_closeout_protocol_projection(baseline_root)
        except CloseoutPlanReceiptError as exc:
            return {"ready": False, "state": "error", "errors": [str(exc)]}
        for lakefile in ("lakefile.toml", "lakefile.lean"):
            content, blob_error = _git_blob_at_rollout(root, lakefile)
            if blob_error:
                return {"ready": False, "state": "error", "errors": [blob_error]}
            if content is not None:
                (baseline_root / lakefile).write_bytes(content)
        baseline_routing, routing_error = lake_routing_projection(baseline_root, paper)
    if baseline_target_config != receipt.get("target_audit_config_projection"):
        errors.append("target audit configuration differs from rollout")
    if baseline_protocol != receipt.get("strict_closeout_protocol_projection"):
        errors.append("semantic review protocol differs from rollout")
    if baseline_routing is None:
        return {
            "ready": False,
            "state": "error",
            "errors": [routing_error or "trusted rollout Lake routing is unavailable"],
        }
    if _digest(baseline_routing) != receipt.get("lake_routing_projection_sha256"):
        errors.append("target Lake routing differs from rollout")

    return {
        "ready": not errors,
        "state": "current" if not errors else "material_changed",
        "errors": errors,
        "baseline_commit": INTAKE_FREEZE_LEGACY_BASELINE_COMMIT,
        "acceptance_credential": False,
    }


def intake_freeze_readiness(
    folder: Path, *, repository_root: Path | None = None
) -> dict[str, Any]:
    """Validate a historical intake seal when tracked status selects it."""

    root = (repository_root or ROOT).resolve()

    status_path = folder / "status.json"
    try:
        status = json.loads(status_path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError) as exc:
        return {
            "ready": False,
            "state": "invalid",
            "errors": [f"cannot read status marker: {exc}"],
        }
    if not isinstance(status, Mapping):
        return {
            "ready": False,
            "state": "invalid",
            "errors": ["status.json must be a JSON object"],
        }
    if "intake_freeze_required" not in status:
        if not _paper_predates_intake_freeze_baseline(str(root), folder.name):
            return {
                "ready": False,
                "state": "prospective_marker_missing",
                "errors": [
                    "paper is outside the trusted intake-rollout cohort but its "
                    "intake_freeze_required marker is missing"
                ],
            }
        return {
            "ready": True,
            "state": "legacy_not_configured",
            "reason": "existing status predates the prospective intake seal",
            "errors": [],
        }
    if status.get("intake_freeze_required") is not True:
        return {
            "ready": False,
            "state": "invalid",
            "errors": [
                "tracked intake_freeze_required marker must be exactly true when present"
            ],
        }

    path = folder / "audit" / "intake_freeze.json"
    if not path.is_file():
        return {
            "ready": False,
            "state": "missing",
            "errors": ["required prospective intake freeze is missing"],
        }
    try:
        payload = json.loads(path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError) as exc:
        return {"ready": False, "state": "invalid", "errors": [str(exc)]}
    errors: list[str] = []
    if not isinstance(payload, dict) or payload.get("schema") != 1:
        errors.append("intake freeze must be a schema-1 JSON object")
        payload = {}
    if payload.get("paper") != folder.name:
        errors.append("intake freeze paper does not match its folder")
    if (
        payload.get("state") != "sealed"
        or payload.get("inventory_complete") is not True
    ):
        errors.append(
            "intake freeze is not sealed with a complete named-theory inventory"
        )
    if payload.get("source_item_identity") != INTAKE_SOURCE_IDENTITY:
        errors.append(
            "intake freeze does not declare the normalized semantic identity scheme"
        )

    source_map_path = folder / "audit" / "paper_statement_map.json"
    try:
        source_map = json.loads(source_map_path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError) as exc:
        errors.append(f"cannot read canonical source map: {exc}")
        source_map = {}
    if not isinstance(source_map, Mapping):
        errors.append("canonical source map must be a JSON object")
        source_map = {}

    errors.extend(
        f"source-text companion: {issue.message}"
        for issue in source_text_companion_validation_issues(
            folder, source_map, repository_root=root
        )
    )

    artifact_text = str(payload.get("source_artifact_path") or "").strip()
    artifact_digest = str(payload.get("source_artifact_sha256") or "").strip().lower()
    map_artifact_text = str(source_map.get("source_artifact_path") or "").strip()
    map_artifact_digest = (
        str(source_map.get("source_artifact_sha256") or "").strip().lower()
    )
    if artifact_text != map_artifact_text or artifact_digest != map_artifact_digest:
        errors.append(
            "intake freeze source artifact identity does not equal the canonical source-map identity"
        )

    semantic_artifact_text, semantic_artifact_digest = semantic_review_source_identity(
        source_map
    )

    def paper_local_path(raw_path: str) -> Path | None:
        if not raw_path:
            return None
        unresolved = Path(raw_path)
        candidate = (
            unresolved.resolve()
            if unresolved.is_absolute()
            else (
                (root / unresolved).resolve()
                if unresolved.parts[:1] == ("papers",)
                else (folder / unresolved).resolve()
            )
        )
        try:
            candidate.relative_to(folder.resolve())
        except ValueError:
            return None
        return candidate

    artifact = paper_local_path(map_artifact_text)
    artifact_bytes: bytes | None = None
    if (
        artifact is None
        or not SHA256_RE.fullmatch(map_artifact_digest)
        or not artifact.is_file()
    ):
        errors.append(
            "canonical source map has no readable paper-local byte-pinned artifact"
        )
    else:
        try:
            artifact_bytes = artifact.read_bytes()
        except OSError as exc:
            errors.append(f"cannot read canonical source artifact: {exc}")
        else:
            if hashlib.sha256(artifact_bytes).hexdigest() != map_artifact_digest:
                errors.append("canonical source-map artifact SHA-256 is stale")

    atom_artifact_bytes = artifact_bytes
    if artifact is not None and artifact.suffix.lower() == ".pdf":
        receipt = payload.get("source_text_artifact")
        if not isinstance(receipt, Mapping) or receipt.get("schema") != 1:
            errors.append(
                "PDF intake freeze requires a schema-1 normalized source-text artifact receipt"
            )
            atom_artifact_bytes = None
        else:
            text_path_text = str(receipt.get("path") or "").strip()
            text_digest = str(receipt.get("sha256") or "").strip().lower()
            text_path = paper_local_path(text_path_text)
            extraction = receipt.get("extraction")
            if (
                receipt.get("normalization") != "utf8-lf-v1"
                or text_path is None
                or text_path.suffix.lower() == ".pdf"
                or not SHA256_RE.fullmatch(text_digest)
                or not text_path.is_file()
            ):
                errors.append(
                    "PDF source-text receipt has no readable normalized paper-local text artifact"
                )
                atom_artifact_bytes = None
            else:
                try:
                    text_bytes = text_path.read_bytes()
                    text_bytes.decode("utf-8")
                except (OSError, UnicodeDecodeError) as exc:
                    errors.append(
                        f"cannot read normalized PDF source text as UTF-8: {exc}"
                    )
                    atom_artifact_bytes = None
                else:
                    if b"\r" in text_bytes:
                        errors.append("PDF source text is not LF-normalized")
                        atom_artifact_bytes = None
                    elif hashlib.sha256(text_bytes).hexdigest() != text_digest:
                        errors.append("PDF source-text artifact SHA-256 is stale")
                        atom_artifact_bytes = None
                    else:
                        atom_artifact_bytes = text_bytes
            if not isinstance(extraction, Mapping) or extraction.get("schema") != 1:
                errors.append("PDF source-text artifact lacks an extraction receipt")
                atom_artifact_bytes = None
            else:
                extraction_path = str(
                    extraction.get("source_artifact_path") or ""
                ).strip()
                extraction_digest = (
                    str(extraction.get("source_artifact_sha256") or "").strip().lower()
                )
                options = extraction.get("options")
                if (
                    extraction_path != map_artifact_text
                    or extraction_digest != map_artifact_digest
                    or extraction.get("tool") != "pdftotext"
                    or not isinstance(options, list)
                    or not all(isinstance(option, str) for option in options)
                ):
                    errors.append(
                        "PDF extraction receipt is not bound to the canonical source-map artifact"
                    )
                    atom_artifact_bytes = None

    # Source-atom byte offsets and source-to-Spec rows may use a separately
    # pinned visual transcription when the complete canonical extraction has
    # damaged mathematical glyphs.  The companion validator above authenticates
    # that exceptional route; never infer it from an item filename.
    if (
        semantic_artifact_text != map_artifact_text
        or semantic_artifact_digest != map_artifact_digest
    ):
        semantic_artifact = paper_local_path(semantic_artifact_text)
        if (
            semantic_artifact is None
            or not SHA256_RE.fullmatch(semantic_artifact_digest)
            or not semantic_artifact.is_file()
        ):
            errors.append(
                "semantic-review source artifact has no readable paper-local byte pin"
            )
            atom_artifact_bytes = None
        else:
            try:
                semantic_bytes = semantic_artifact.read_bytes()
                semantic_bytes.decode("utf-8")
            except (OSError, UnicodeDecodeError) as exc:
                errors.append(
                    f"cannot read semantic-review source artifact as UTF-8: {exc}"
                )
                atom_artifact_bytes = None
            else:
                if hashlib.sha256(semantic_bytes).hexdigest() != semantic_artifact_digest:
                    errors.append("semantic-review source artifact SHA-256 is stale")
                    atom_artifact_bytes = None
                else:
                    atom_artifact_bytes = semantic_bytes

    source_items_by_identity: dict[
        tuple[str, str], list[tuple[str, Mapping[str, Any]]]
    ] = {}
    if isinstance(source_map, Mapping):
        for key, source_item in inventory_from_source_map(folder, source_map).items():
            location = str(source_item.get("source_location") or "").strip()
            statement_sha = (
                str(source_item.get("statement_sha256") or "").strip().lower()
            )
            if location and SHA256_RE.fullmatch(statement_sha):
                source_items_by_identity.setdefault(
                    (location, statement_sha), []
                ).append((key, source_item))

    raw_items = payload.get("items")
    items = raw_items if isinstance(raw_items, list) else []
    if not items:
        errors.append("intake freeze has no source obligations")
    orders: list[int] = []
    identities: set[tuple[str, str]] = set()
    for index, raw_item in enumerate(items, start=1):
        if not isinstance(raw_item, Mapping):
            errors.append(f"intake item {index} is not an object")
            continue
        location = str(raw_item.get("source_location") or "").strip()
        statement_sha = (
            str(raw_item.get("source_statement_sha256") or "").strip().lower()
        )
        if not location or not SHA256_RE.fullmatch(statement_sha):
            errors.append(
                f"intake item {index} lacks a locator-bound statement identity"
            )
        elif (location, statement_sha) in identities:
            errors.append(f"intake item {index} duplicates a semantic source identity")
        else:
            identities.add((location, statement_sha))
        mapped_items = source_items_by_identity.get((location, statement_sha), [])
        if len(mapped_items) != 1:
            errors.append(
                f"intake item {index} does not identify exactly one current source-map item by location and normalized statement"
            )
        else:
            mapped_item = mapped_items[0][1]
            if (
                str(mapped_item.get("source_artifact_path") or "").strip()
                != semantic_artifact_text
                or str(mapped_item.get("source_artifact_sha256") or "").strip().lower()
                != semantic_artifact_digest
            ):
                errors.append(
                    f"intake item {index} source-map route is not bound to the semantic-review artifact"
                )
        order = raw_item.get("dependency_order")
        if not isinstance(order, int) or isinstance(order, bool) or order <= 0:
            errors.append(f"intake item {index} has no positive dependency order")
        else:
            orders.append(order)
        owner = str(raw_item.get("owner") or "").strip().lower()
        if not owner or owner == "unassigned":
            errors.append(f"intake item {index} has no proof owner")
        conditions = raw_item.get("acceptance_conditions")
        if (
            not isinstance(conditions, list)
            or not conditions
            or not all(
                isinstance(condition, str) and condition.strip()
                for condition in conditions
            )
        ):
            errors.append(f"intake item {index} has incomplete acceptance conditions")
        atoms = raw_item.get("source_atoms")
        if not isinstance(atoms, list) or not atoms:
            errors.append(f"intake item {index} has no byte-pinned source atoms")
            continue
        for atom_index, atom in enumerate(atoms, start=1):
            if not isinstance(atom, Mapping):
                errors.append(f"intake item {index} atom {atom_index} is not an object")
                continue
            quote = str(atom.get("quoted_text") or "")
            quote_sha = str(atom.get("quoted_text_sha256") or "").strip().lower()
            atom_location = str(atom.get("source_location") or "").strip()
            byte_start = atom.get("byte_start")
            byte_end = atom.get("byte_end")
            exact_slice = (
                atom_artifact_bytes[byte_start:byte_end]
                if atom_artifact_bytes is not None
                and isinstance(byte_start, int)
                and not isinstance(byte_start, bool)
                and isinstance(byte_end, int)
                and not isinstance(byte_end, bool)
                and 0 <= byte_start < byte_end <= len(atom_artifact_bytes)
                else None
            )
            if (
                not quote.strip()
                or not atom_location
                or not SHA256_RE.fullmatch(quote_sha)
                or hashlib.sha256(quote.encode("utf-8")).hexdigest() != quote_sha
                or exact_slice != quote.encode("utf-8")
            ):
                errors.append(
                    f"intake item {index} atom {atom_index} lacks an exact artifact byte slice"
                )
    if orders and sorted(orders) != list(range(1, len(items) + 1)):
        errors.append("intake dependency order is not a total 1..N order")
    expected_identities = set(source_items_by_identity)
    if identities != expected_identities:
        missing_count = len(expected_identities - identities)
        unexpected_count = len(identities - expected_identities)
        errors.append(
            "intake freeze identities do not exactly equal the current source-map "
            f"inventory (missing={missing_count}, unexpected={unexpected_count})"
        )
    return {
        "ready": not errors,
        "state": "sealed" if not errors else "incomplete",
        "path": str(path.relative_to(root)),
        "errors": errors,
    }


def reviewed_source_inventory_readiness(
    folder: Path, *, repository_root: Path | None = None
) -> dict[str, Any]:
    """Validate one curator-owned plan against its exact materialized source map."""

    root = (repository_root or ROOT).resolve()
    status_path = folder / "status.json"
    map_path = folder / "audit" / "paper_statement_map.json"
    config_path = folder / "audit" / SOURCE_INVENTORY_REVIEW_CONFIG

    def load_object(path: Path, label: str) -> tuple[dict[str, Any], str]:
        try:
            payload = json.loads(path.read_text(encoding="utf-8"))
        except (OSError, json.JSONDecodeError) as exc:
            return {}, f"cannot read {label}: {exc}"
        if not isinstance(payload, dict):
            return {}, f"{label} must be a JSON object"
        return payload, ""

    status, status_error = load_object(status_path, "status marker")
    if status_error:
        return {"ready": False, "state": "invalid", "errors": [status_error]}
    if status.get(SOURCE_INVENTORY_REVIEW_REQUIRED_FIELD) is not True:
        return {
            "ready": False,
            "state": "invalid",
            "errors": [
                f"tracked {SOURCE_INVENTORY_REVIEW_REQUIRED_FIELD} marker must be "
                "exactly true when present"
            ],
        }
    if "intake_freeze_required" in status:
        return {
            "ready": False,
            "state": "ambiguous",
            "errors": [
                "status selects both reviewed source-inventory and legacy intake-freeze authorities"
            ],
        }

    source_map, map_error = load_object(map_path, "canonical source map")
    config, config_error = load_object(config_path, "source-inventory review plan")
    errors = [error for error in (map_error, config_error) if error]
    if errors:
        return {"ready": False, "state": "invalid", "errors": errors}
    if config.get("paper") != folder.name:
        errors.append("source-inventory review plan paper does not match its folder")
    inventory_plan = config.get("source_named_result_inventory_review")
    if not isinstance(inventory_plan, Mapping):
        errors.append(
            "source-inventory review configuration lacks its reviewed decision plan"
        )
    elif not isinstance(inventory_plan.get("candidate_presentations"), list):
        errors.append(
            "source-inventory review plan must explicitly classify the complete "
            "source-only candidate surface in candidate_presentations, even when empty"
        )
    review = source_map.get("source_named_result_inventory_review")
    if not isinstance(review, Mapping) or review.get("complete") is not True:
        errors.append(
            "canonical source map lacks a complete reviewed source inventory"
        )
    elif not isinstance(review.get("candidate_presentations"), list):
        errors.append(
            "canonical source map lacks the materialized source-only candidate ledger"
        )
    elif not SHA256_RE.fullmatch(
        str(review.get("discovered_candidate_presentation_sha256") or "")
        .strip()
        .lower()
    ):
        errors.append(
            "canonical source map lacks the current candidate-presentation digest"
        )
    try:
        from scripts.prepare_v11_source_map import PreparationError, prepare

        prepared = prepare(source_map, config, folder=folder)
    except (OSError, PreparationError, RuntimeError, ValueError) as exc:
        errors.append(f"cannot materialize reviewed source inventory: {exc}")
    else:
        if prepared != source_map:
            errors.append(
                "canonical source map is not the exact current materialization of "
                "its reviewed source-inventory plan"
            )
    try:
        relative_config = config_path.resolve().relative_to(root)
    except ValueError:
        errors.append("source-inventory review plan is outside the repository")
        relative_config = config_path
    return {
        "ready": not errors,
        "state": "current" if not errors else "incomplete",
        "authority": "reviewed_source_inventory_v1",
        "path": str(relative_config),
        "errors": errors,
        "acceptance_credential": False,
    }


def _canonical_source_surface_errors(
    folder: Path, *, status: Mapping[str, Any]
) -> list[str]:
    """Return source-only canonical-map failures before any Lean acquisition.

    A current paper may retain a legacy intake marker while already carrying a
    canonical source map.  The marker decides which *intake authority* it
    uses; it must not postpone validation of that map until after a graph,
    review batch, or final adversarial review has been acquired.  The evidence
    validator below is deliberately source-only: it reads the byte-pinned
    source, its named-result inventory, anchors, and source contexts, but does
    not elaborate Lean, issue a receipt, or inspect semantic-review evidence.

    Papers without a source map remain on their selected historical intake
    route.  Once a map is present, however, its source surface is a first-phase
    closeout obligation rather than a terminal diagnostic.
    """

    mathematical_status = str(status.get("status") or "").strip().lower()
    map_path = folder / "audit" / "paper_statement_map.json"
    if not map_path.exists():
        # Historical status fixtures without a declared mathematical status are
        # still readable by intake-planning tools.  A declared paper status,
        # however, selects an actual closeout route and must supply the
        # canonical source map before any later evidence work begins.
        return (
            [
                "canonical source-surface preflight requires "
                "audit/paper_statement_map.json"
            ]
            if mathematical_status
            else []
        )
    if not mathematical_status:
        # Status-less fixtures and historical intake-planning records do not
        # select a closeout route.  Keep them readable; the declared-status
        # branch above is the fail-closed boundary for an actual paper
        # closeout.
        return []
    try:
        # Keep this lazy so prospective intake validation remains importable by
        # lightweight planning tools.  `check_source_manifest` is the one
        # shared source-only validator; duplicating its source parsing here
        # would allow the two gates to drift.
        from scripts.source_manifest_validation import check_source_manifest

        findings = check_source_manifest(
            folder,
            mathematical_status,
            require_source_bytes=True,
        )
    except (OSError, RuntimeError, ValueError, json.JSONDecodeError) as exc:
        return [f"canonical source-surface preflight is unavailable: {exc}"]
    return [
        str(finding.message).strip()
        for finding in findings
        if str(getattr(finding, "severity", "")).upper() == "ERROR"
        and str(getattr(finding, "message", "")).strip()
    ]


def source_intake_readiness(
    folder: Path, *, repository_root: Path | None = None
) -> dict[str, Any]:
    """Validate intake authority and the canonical source surface, if present.

    The canonical source surface is intentionally validated first in the
    closeout executor, before it acquires a Lean graph or schedules reviewers.
    """

    try:
        status = json.loads((folder / "status.json").read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError) as exc:
        return {
            "ready": False,
            "state": "invalid",
            "errors": [f"cannot read status marker: {exc}"],
        }
    if not isinstance(status, Mapping):
        return {
            "ready": False,
            "state": "invalid",
            "errors": ["status.json must be a JSON object"],
        }
    if SOURCE_INVENTORY_REVIEW_REQUIRED_FIELD in status:
        readiness = reviewed_source_inventory_readiness(
            folder, repository_root=repository_root
        )
    else:
        readiness = intake_freeze_readiness(folder, repository_root=repository_root)

    source_errors = _canonical_source_surface_errors(folder, status=status)
    if not source_errors:
        return readiness
    existing_errors = readiness.get("errors")
    return {
        **readiness,
        "ready": False,
        "state": "incomplete",
        "errors": [
            *(existing_errors if isinstance(existing_errors, list) else []),
            *[
                "canonical source-surface preflight: " + error
                for error in source_errors
            ],
        ],
    }
