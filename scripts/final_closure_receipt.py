#!/usr/bin/env python3
"""Validate current graph-native or historical paper-closure credentials.

The selected accepted obligation graph is the current sole machine acceptance
credential; schema-6 ``FINAL_CLOSURE_RECEIPT.md`` is only its human-facing
pointer. Validation dispatches historical schemas under their recorded rules.
Historical schema-2--4 receipts remain readable for direct validation and
explicit migration, but this module no longer manufactures them. Fresh
closeout finalization authenticates the typed strict-stage transaction and
publishes the accepted graph directly.

This module is intentionally independent of ``audit_evidence_integrity`` so
the main evidence gate can use it without a circular import.

Its import-closure-accelerator diagnostic is explicitly non-accepting: a
successful process exit means the inventory completed, not that every carrier
was exact. Consumers must inspect ``exact_count`` and ``miss_count``.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import re
import shlex
import subprocess
import sys
from dataclasses import dataclass
from datetime import date
from pathlib import Path, PurePosixPath
from typing import Any, Callable, Iterable, Mapping

ROOT = Path(
    os.environ.get("APPLIEDMODELINGLIB_REPO_ROOT", Path(__file__).resolve().parents[1])
).resolve()
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts.check_formalization_engine_revision import (
    EngineRevisionError,
    validate_runtime_engine_registration,
    validated_runtime_engine_revision_ledger,
)
from scripts.closeout_plan_receipt import (
    CloseoutPlanReceiptError,
    resolved_plan_lean_closure_projection,
)
from scripts.formalization_protocol import formalization_review_protocol_digest
from scripts.lean_import_closure import (
    WorktreeImportClosureProvider,
    lean_import_closure_payload_sha256,
    lean_import_closure_receipt_payload,
    validated_lean_import_closure_payload,
    validated_lean_import_closure_receipt_payload,
)
from scripts.lean_process_diagnostics import (
    bounded_lean_diagnostic_excerpt,
    lean_diagnostic_failure_reason,
)
from scripts.paper_build_command import is_exact_portable_paper_build_command
from scripts.source_archive_surface import source_archive_surface_validation_issues
from scripts.source_coverage_scope import (
    explicit_raw_source_spec_screening_requested,
)
from scripts.tomllib_compat import tomllib

RECEIPT_NAME = "FINAL_CLOSURE_RECEIPT.md"
RECEIPT_SCHEMA = 4
LEGACY_RECEIPT_SCHEMAS = frozenset({2, 3, RECEIPT_SCHEMA})
OBLIGATION_RECEIPT_SCHEMA = 5
ACCEPTED_GRAPH_RECEIPT_SCHEMA = 6
OBLIGATION_RECEIPT_SCHEMAS = frozenset(
    {OBLIGATION_RECEIPT_SCHEMA, ACCEPTED_GRAPH_RECEIPT_SCHEMA}
)
FOCUSED_BUILD_RECEIPT_NAME = "FOCUSED_BUILD_RECEIPT.json"
FOCUSED_BUILD_RECEIPT_SCHEMA = 2
AUTHENTICATED_CLOSURE_FOCUSED_BUILD_RECEIPT_SCHEMA = 3
LEGACY_FOCUSED_BUILD_RECEIPT_SCHEMAS = frozenset(
    {
        1,
        FOCUSED_BUILD_RECEIPT_SCHEMA,
        AUTHENTICATED_CLOSURE_FOCUSED_BUILD_RECEIPT_SCHEMA,
    }
)
LEAN_IMPORT_CLOSURE_RECEIPT_NAME = "LEAN_IMPORT_CLOSURE_RECEIPT.json"
LEAN_IMPORT_CLOSURE_RECEIPT_SCHEMA = 1
RAW_SOURCE_RECORD_LANE = "raw-source-record"
DIRECT_SOURCE_ROW_REVIEW_LANE = "direct-source-row-review"
EVIDENCE_LANES = frozenset({RAW_SOURCE_RECORD_LANE, DIRECT_SOURCE_ROW_REVIEW_LANE})
V11_SCREENING_LEDGER_RELATIVE = Path("audit") / "v11_raw_source_spec_screening.json"
SHA256_RE = re.compile(r"^[0-9a-f]{64}$")
GIT_COMMIT_RE = re.compile(r"^[0-9a-f]{40}$")
PAPER_RE = re.compile(r"^[A-Za-z0-9][A-Za-z0-9_.-]*$")
REPORT_EVIDENCE_START_MARKER = "## 12. Detailed Formalization Evidence"


class FinalClosureReceiptError(ValueError):
    """A final closure receipt is missing, malformed, or no longer current."""


@dataclass(frozen=True)
class FinalClosureReceipt:
    """Parsed canonical receipt payload and its source path."""

    path: Path
    payload: Mapping[str, Any]
    terminal_validation_route: str = ""
    terminal_validation_detail: str = ""


def final_closure_receipt_path(root: Path, paper: str) -> Path:
    return root / "papers" / paper / RECEIPT_NAME


def focused_build_receipt_path(root: Path, paper: str) -> Path:
    return root / "papers" / paper / "audit" / FOCUSED_BUILD_RECEIPT_NAME


def lean_import_closure_receipt_path(root: Path, paper: str) -> Path:
    return (
        root
        / "papers"
        / paper
        / "audit"
        / LEAN_IMPORT_CLOSURE_RECEIPT_NAME
    )


def diagnose_exact_import_closure_accelerator(
    root: Path,
    paper: str,
    *,
    provider_factory: Callable[..., Any] | None = None,
) -> dict[str, object]:
    """Diagnose one non-accepting exact import-closure accelerator.

    This deliberately does not load or validate the paper's acceptance
    credential and never invokes Lean semantic recovery.  It answers only
    whether the checked-in portable carrier still matches every current
    source, ownership, build-control, routing, and external-artifact input.
    """

    paper_id = str(paper).strip()
    if PAPER_RE.fullmatch(paper_id) is None:
        return {
            "paper": paper_id,
            "exact_accelerator_current": False,
            "problem": "paper identity is malformed",
        }
    path = lean_import_closure_receipt_path(root, paper_id)
    try:
        raw_receipt = json.loads(path.read_text(encoding="utf-8"))
        receipt = validated_lean_import_closure_receipt_payload(
            raw_receipt,
            paper=paper_id,
        )
        closure = receipt.get("lean_import_closure")
        if not isinstance(closure, dict):
            raise ValueError("Lean import-closure carrier payload is malformed")
        if provider_factory is None:
            from scripts.lean_signature_manifest import (
                RepositoryBuildInputSnapshotProvider,
            )

            provider_factory = RepositoryBuildInputSnapshotProvider
        provider = provider_factory(
            root,
            lean_import_closure_payload=closure,
        )
        if not provider.finalize_unchanged():
            raise ValueError(
                "Lean import-closure inputs changed during the diagnostic"
            )
    except (OSError, UnicodeError, json.JSONDecodeError, ValueError) as exc:
        return {
            "paper": paper_id,
            "exact_accelerator_current": False,
            "problem": str(exc),
        }
    return {
        "paper": paper_id,
        "exact_accelerator_current": True,
        "problem": "",
    }


def diagnose_import_closure_accelerators(
    root: Path,
    *,
    paper: str | None = None,
    provider_factory: Callable[..., Any] | None = None,
) -> dict[str, object]:
    """Return one read-only diagnostic over selected portable carriers."""

    if paper is not None:
        papers = [paper]
    else:
        papers = [
            path.parents[1].name
            for path in sorted(
                (root / "papers").glob(
                    f"*/audit/{LEAN_IMPORT_CLOSURE_RECEIPT_NAME}"
                )
            )
        ]
    items = [
        diagnose_exact_import_closure_accelerator(
            root,
            paper_id,
            provider_factory=provider_factory,
        )
        for paper_id in papers
    ]
    exact_count = sum(
        item["exact_accelerator_current"] is True for item in items
    )
    return {
        "schema": 1,
        "acceptance_credential": False,
        "diagnostic_only": True,
        "paper_count": len(items),
        "exact_count": exact_count,
        "miss_count": len(items) - exact_count,
        "items": items,
    }


def _sha256_bytes(raw: bytes) -> str:
    return hashlib.sha256(raw).hexdigest()


def _sha256_file(path: Path) -> str:
    try:
        return _sha256_bytes(path.read_bytes())
    except OSError as exc:
        raise FinalClosureReceiptError(f"could not read `{path}`: {exc}") from exc


def _required_string(payload: Mapping[str, Any], field: str) -> str:
    value = payload.get(field)
    if not isinstance(value, str) or not value.strip():
        raise FinalClosureReceiptError(f"`{field}` must be a nonempty string")
    return value.strip()


def _required_sha256(payload: Mapping[str, Any], field: str) -> str:
    value = _required_string(payload, field).lower()
    if not SHA256_RE.fullmatch(value):
        raise FinalClosureReceiptError(f"`{field}` must be a lowercase SHA-256")
    return value


def _mapping(payload: Mapping[str, Any], field: str) -> Mapping[str, Any]:
    value = payload.get(field)
    if not isinstance(value, Mapping):
        raise FinalClosureReceiptError(f"`{field}` must be a table")
    return value


def _repository_path(root: Path, raw: str, *, field: str) -> Path:
    path = PurePosixPath(raw)
    if (
        not raw
        or path.is_absolute()
        or "\\" in raw
        or any(part in {"", ".", ".."} for part in path.parts)
    ):
        raise FinalClosureReceiptError(
            f"`{field}.path` must be a repository-relative path without `..`"
        )
    candidate = root / Path(*path.parts)
    try:
        candidate.resolve(strict=False).relative_to(root.resolve())
    except (OSError, RuntimeError, ValueError) as exc:
        raise FinalClosureReceiptError(
            f"`{field}.path` resolves outside the repository"
        ) from exc
    return candidate


def _paper_local_path(root: Path, paper: str, raw: str, *, field: str) -> Path:
    normalized = str(raw).strip()
    path = PurePosixPath(normalized)
    if (
        not normalized
        or path.is_absolute()
        or "\\" in normalized
        or any(part in {"", ".", ".."} for part in path.parts)
    ):
        raise FinalClosureReceiptError(
            f"`{field}.path` must be a paper-local or repository-relative path without `..`"
        )
    paper_dir = root / "papers" / paper
    candidate = (
        _repository_path(root, normalized, field=field)
        if path.parts[:1] == ("papers",)
        else paper_dir.joinpath(*path.parts)
    )
    try:
        candidate.resolve(strict=False).relative_to(paper_dir.resolve())
    except (OSError, RuntimeError, ValueError) as exc:
        raise FinalClosureReceiptError(
            f"`{field}.path` must stay within papers/{paper}"
        ) from exc
    return candidate


def _source_artifact_path_from_map(root: Path, paper: str, raw: str) -> Path:
    """Resolve either accepted map spelling while enforcing paper locality."""

    return _paper_local_path(root, paper, str(raw).strip(), field="source_artifact")


def _read_toml_front_matter(path: Path) -> Mapping[str, Any]:
    try:
        text = path.read_text(encoding="utf-8")
    except (OSError, UnicodeError) as exc:
        raise FinalClosureReceiptError(f"could not read final closure receipt: {exc}") from exc
    lines = text.splitlines(keepends=True)
    if not lines or lines[0].strip() != "+++":
        raise FinalClosureReceiptError("receipt must start with TOML `+++` front matter")
    closing = next(
        (index for index, line in enumerate(lines[1:], start=1) if line.strip() == "+++"),
        None,
    )
    if closing is None:
        raise FinalClosureReceiptError("receipt TOML front matter has no closing `+++`")
    try:
        payload = tomllib.loads("".join(lines[1:closing]))
    except (TypeError, tomllib.TOMLDecodeError) as exc:
        raise FinalClosureReceiptError(f"receipt TOML front matter is invalid: {exc}") from exc
    if not isinstance(payload, Mapping):  # Defensive for alternate TOML backends.
        raise FinalClosureReceiptError("receipt TOML front matter must be an object")
    return payload


def load_final_closure_receipt(root: Path, paper: str) -> FinalClosureReceipt:
    if not PAPER_RE.fullmatch(paper):
        raise FinalClosureReceiptError("paper identifier is malformed")
    path = final_closure_receipt_path(root, paper)
    if not path.is_file():
        raise FinalClosureReceiptError(f"missing canonical receipt `{path.relative_to(root)}`")
    return FinalClosureReceipt(path=path, payload=_read_toml_front_matter(path))


def _expect_exact_keys(
    value: Mapping[str, Any], *, field: str, required: set[str]
) -> None:
    actual = set(value)
    if actual != required:
        missing = sorted(required - actual)
        extra = sorted(actual - required)
        parts: list[str] = []
        if missing:
            parts.append("missing " + ", ".join(missing))
        if extra:
            parts.append("unexpected " + ", ".join(extra))
        raise FinalClosureReceiptError(f"`{field}` has " + "; ".join(parts))


def _validate_file_pin(
    root: Path,
    paper: str,
    payload: Mapping[str, Any],
    *,
    field: str,
    expected_path: Path | None = None,
    paper_local: bool = True,
) -> Path:
    pin = _mapping(payload, field)
    _expect_exact_keys(pin, field=field, required={"path", "sha256"})
    raw_path = _required_string(pin, "path")
    candidate = (
        _paper_local_path(root, paper, raw_path, field=field)
        if paper_local
        else _repository_path(root, raw_path, field=field)
    )
    if expected_path is not None and candidate.resolve(strict=False) != expected_path.resolve(
        strict=False
    ):
        raise FinalClosureReceiptError(
            f"`{field}.path` must be `{expected_path.relative_to(root).as_posix()}`"
        )
    expected_hash = _required_sha256(pin, "sha256")
    actual_hash = _sha256_file(candidate)
    if actual_hash != expected_hash:
        raise FinalClosureReceiptError(
            f"`{field}` SHA-256 is stale for `{candidate.relative_to(root)}`"
        )
    return candidate


def _review_ledger_selected_bytes(path: Path, *, content_start: str | None) -> bytes:
    """Return the evidence-bearing bytes of a review ledger.

    A final validation report has a deliberately editable paper-facing front
    section.  Its detailed evidence begins at a stable heading, so bind that
    evidence section rather than making a prose clarification in Sections 1--11
    invalidate the paper's canonical closure.  A standalone row-review ledger
    remains byte-pinned in full.
    """

    try:
        raw = path.read_bytes()
    except OSError as exc:
        raise FinalClosureReceiptError(f"could not read `{path}`: {exc}") from exc
    if content_start is None:
        return raw
    try:
        text = raw.decode("utf-8")
    except UnicodeDecodeError as exc:
        raise FinalClosureReceiptError(
            f"review ledger `{path}` cannot use a text evidence boundary"
        ) from exc
    matches = [
        match.start()
        for match in re.finditer(
            rf"(?m)^{re.escape(content_start)}\s*$",
            text,
        )
    ]
    if len(matches) != 1:
        raise FinalClosureReceiptError(
            f"review ledger evidence boundary `{content_start}` must occur exactly once"
        )
    return text[matches[0] :].encode("utf-8")


def _validate_review_ledger_pin(
    root: Path,
    paper: str,
    payload: Mapping[str, Any],
) -> Path:
    """Validate the source-review bytes without hashing report front matter."""

    pin = _mapping(payload, "review_ledger")
    allowed = {"path", "sha256", "content_start"}
    unexpected = set(pin) - allowed
    if unexpected:
        raise FinalClosureReceiptError(
            "`review_ledger` has unexpected " + ", ".join(sorted(unexpected))
        )
    required = {"path", "sha256"}
    missing = required - set(pin)
    if missing:
        raise FinalClosureReceiptError(
            "`review_ledger` missing " + ", ".join(sorted(missing))
        )
    raw_path = _required_string(pin, "path")
    path = _repository_path(root, raw_path, field="review_ledger")
    try:
        path.resolve(strict=False).relative_to((root / "papers" / paper).resolve())
    except (OSError, RuntimeError, ValueError) as exc:
        raise FinalClosureReceiptError("`review_ledger.path` must stay within this paper") from exc
    raw_boundary = pin.get("content_start")
    if raw_boundary is not None and (
        not isinstance(raw_boundary, str) or not raw_boundary.strip()
    ):
        raise FinalClosureReceiptError("`review_ledger.content_start` must be a nonempty string")
    content_start = raw_boundary.strip() if isinstance(raw_boundary, str) else None
    if path.name == "FINAL_VALIDATION_REPORT.md" and content_start != REPORT_EVIDENCE_START_MARKER:
        raise FinalClosureReceiptError(
            "`review_ledger` must bind the detailed-evidence section of FINAL_VALIDATION_REPORT.md"
        )
    expected_hash = _required_sha256(pin, "sha256")
    actual_hash = _sha256_bytes(
        _review_ledger_selected_bytes(path, content_start=content_start)
    )
    if actual_hash != expected_hash:
        raise FinalClosureReceiptError(
            f"`review_ledger` SHA-256 is stale for `{path.relative_to(root)}`"
        )
    return path


def _lean_import_closure_receipt_payload(
    paper: str, closure: object
) -> dict[str, Any]:
    return dict(lean_import_closure_receipt_payload(paper, closure))


def _write_lean_import_closure_receipt(
    root: Path, paper: str, closure: object
) -> Path:
    payload = _lean_import_closure_receipt_payload(paper, closure)
    path = lean_import_closure_receipt_path(root, paper)
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(
        json.dumps(payload, sort_keys=True, separators=(",", ":")) + "\n",
        encoding="utf-8",
    )
    return path


def _saved_interface_closure_candidates(
    root: Path, paper: str
) -> Iterable[dict[str, object]]:
    """Yield canonical Lean-emitted closures from durable or local carriers."""

    receipt_path = lean_import_closure_receipt_path(root, paper)
    try:
        payload = json.loads(receipt_path.read_text(encoding="utf-8"))
    except (OSError, UnicodeError, json.JSONDecodeError):
        payload = None
    if isinstance(payload, Mapping):
        try:
            validated_receipt = validated_lean_import_closure_receipt_payload(
                payload, paper=paper
            )
        except ValueError:
            pass
        else:
            closure = validated_receipt.get("lean_import_closure")
            assert isinstance(closure, dict)
            yield closure

    # Existing closed papers may predate the durable carrier. Their ignored,
    # content-addressed operational plan contains the exact same Lean-emitted
    # closure. It may locate a candidate but cannot authorize it: the caller
    # below requires the canonical receipt digest and revalidates every current
    # source, association, control, external artifact, and mutation guard.
    trace = root / "papers" / paper / ".review_traces"
    for plan_path in sorted(
        trace.glob("closeout_execution_plan*.json"), reverse=True
    ):
        try:
            plan = json.loads(plan_path.read_text(encoding="utf-8"))
            projection = resolved_plan_lean_closure_projection(root, plan)
            closure = validated_lean_import_closure_payload(
                projection.get("lean_import_closure")
            )
        except (
            OSError,
            UnicodeError,
            json.JSONDecodeError,
            ValueError,
            CloseoutPlanReceiptError,
        ):
            continue
        yield closure


def _validated_saved_interface_closure(
    root: Path,
    paper: str,
    expected_identity: str,
    *,
    entrypoint: str | None = None,
    closure_provider_factory: Callable[[Path], Any] | None = None,
) -> tuple[str, dict[str, object]] | None:
    factory = closure_provider_factory or (
        lambda repository_root: WorktreeImportClosureProvider(
            repository_root, eager_source_snapshot=False
        )
    )
    selected_entrypoint = entrypoint or f"papers/{paper}/PaperInterface.lean"
    for closure in _saved_interface_closure_candidates(root, paper):
        if lean_import_closure_payload_sha256(closure) != expected_identity:
            continue
        provider = factory(root)
        identity, problem = provider.identity_from_saved_closure(
            selected_entrypoint, closure
        )
        if identity != expected_identity or problem is not None:
            continue
        if provider.finalization_problems():
            continue
        return expected_identity, closure
    return None


def _current_interface_closure(
    root: Path,
    paper: str,
    *,
    closure_provider_factory: Callable[[Path], Any] | None = None,
    expected_identity: str | None = None,
    persist_saved_closure: bool = False,
    entrypoint: str | None = None,
) -> str:
    # Final-receipt validation needs only the selected PaperInterface closure.
    # Snapshotting every tracked Lean source in a large monorepo before asking
    # Lean for that one closure used several GiB without strengthening the
    # identity.  The provider's lazy mode still authenticates every source in
    # the Lean-emitted closure and rechecks all of them at finalization.
    if expected_identity is not None:
        saved = _validated_saved_interface_closure(
            root,
            paper,
            expected_identity,
            entrypoint=entrypoint,
            closure_provider_factory=closure_provider_factory,
        )
        if saved is not None:
            identity, closure = saved
            if persist_saved_closure:
                _write_lean_import_closure_receipt(root, paper, closure)
            return identity

    factory = closure_provider_factory or (
        lambda repository_root: WorktreeImportClosureProvider(
            repository_root, eager_source_snapshot=False
        )
    )
    provider = factory(root)
    selected_entrypoint = entrypoint or f"papers/{paper}/PaperInterface.lean"
    record_for_entrypoint = getattr(provider, "record_for_entrypoint", None)
    if callable(record_for_entrypoint):
        closure, problem = record_for_entrypoint(selected_entrypoint)
        identity = (
            lean_import_closure_payload_sha256(closure)
            if closure is not None
            else None
        )
    else:  # Test doubles and historical injected providers.
        closure = None
        identity, problem = provider.identity_for_entrypoint(selected_entrypoint)
    if identity is None or problem is not None:
        raise FinalClosureReceiptError(
            "could not establish current transitive PaperInterface closure: "
            + str(problem or "unknown closure failure")
        )
    problems = provider.finalization_problems()
    if problems:
        raise FinalClosureReceiptError(
            "PaperInterface closure changed while validated: " + str(problems[0])
        )
    if expected_identity is not None and identity != expected_identity:
        raise FinalClosureReceiptError(
            "PaperInterface transitive import-closure SHA-256 is stale"
        )
    if persist_saved_closure and closure is not None:
        _write_lean_import_closure_receipt(root, paper, closure)
    return identity


def validate_final_closure_receipt(
    root: Path,
    paper: str,
    *,
    required_lane: str | None = None,
    allow_missing_source_bytes: bool = False,
    closure_provider_factory: Callable[[Path], Any] | None = None,
) -> FinalClosureReceipt:
    """Fail closed unless the one paper-local receipt binds every current input.

    A public structural checkout may intentionally omit licensed source bytes.
    In that mode, retain the exact path and statement-map hash checks, but use
    the receipt's immutable source pin instead of trying to read absent bytes.
    This is validation of an already-issued receipt, never permission to issue
    a new one without the canonical source artifact.
    """

    receipt = load_final_closure_receipt(root, paper)
    payload = receipt.payload
    schema = payload.get("schema")
    if schema == 6 and allow_missing_source_bytes:
        source_map = json.loads((root / "papers" / paper / "audit" / "paper_statement_map.json").read_text())
        if "source_artifact_path" not in source_map:
            try:
                from scripts.obligation_closure_credential import (
                    ObligationClosureCredentialError,
                    validate_public_recorded_graph_inputs,
                )
                validate_public_recorded_graph_inputs(root, paper, payload)
            except (ObligationClosureCredentialError, ValueError, RuntimeError, OSError) as exc:
                raise FinalClosureReceiptError(str(exc)) from exc
            return FinalClosureReceipt(
                path=receipt.path,
                payload=receipt.payload,
                terminal_validation_route="public_recorded_graph",
                terminal_validation_detail=(
                    "Recorded graph and current Lean inputs verified; source files and "
                    "private review records are withheld. No new acceptance is issued."
                ),
            )
    if schema in OBLIGATION_RECEIPT_SCHEMAS:
        try:
            from scripts.obligation_closure_credential import (
                ObligationClosureCredentialError,
                validate_obligation_closure_receipt,
            )
            verified = validate_obligation_closure_receipt(
                root,
                paper,
                receipt_path=receipt.path,
                payload=payload,
                allow_missing_source_bytes=allow_missing_source_bytes,
            )
        except ObligationClosureCredentialError as exc:
            raise FinalClosureReceiptError(str(exc)) from exc
        return FinalClosureReceipt(
            path=receipt.path,
            payload=receipt.payload,
            terminal_validation_route=verified.terminal_validation_route,
            terminal_validation_detail=verified.terminal_validation_detail,
        )
    if schema not in LEGACY_RECEIPT_SCHEMAS:
        expected = ", ".join(
            str(value)
            for value in sorted((*LEGACY_RECEIPT_SCHEMAS, *OBLIGATION_RECEIPT_SCHEMAS))
        )
        raise FinalClosureReceiptError(f"`schema` must equal one of {expected}")
    if _required_string(payload, "paper") != paper:
        raise FinalClosureReceiptError("receipt `paper` does not match its folder")
    if _required_string(payload, "closure_status") != "current":
        raise FinalClosureReceiptError("receipt `closure_status` must be `current`")
    lane = _required_string(payload, "evidence_lane")
    if lane not in EVIDENCE_LANES:
        raise FinalClosureReceiptError("receipt `evidence_lane` is unsupported")
    if required_lane is not None and lane != required_lane:
        raise FinalClosureReceiptError(
            f"receipt evidence lane is `{lane}`, expected `{required_lane}`"
        )

    allowed = {
        "schema",
        "paper",
        "closure_status",
        "evidence_lane",
        "source_artifact",
        "statement_map",
        "paper_interface_closure",
        "review_ledger",
        "focused_build",
        "protocol",
        "closed_at",
    }
    if schema == RECEIPT_SCHEMA:
        allowed.add("engine")
    if lane == RAW_SOURCE_RECORD_LANE:
        allowed.add("raw_source_record")
    if schema in {3, RECEIPT_SCHEMA}:
        allowed.add("focused_build_receipt")
    _expect_exact_keys(payload, field="receipt", required=allowed)

    if schema == RECEIPT_SCHEMA:
        engine = _mapping(payload, "engine")
        _expect_exact_keys(
            engine,
            field="engine",
            required={
                "revision_sequence",
                "engine_tree_sha256",
                "formalization_review_protocol_sha256",
            },
        )
        sequence = engine.get("revision_sequence")
        if not isinstance(sequence, int) or isinstance(sequence, bool) or sequence < 1:
            raise FinalClosureReceiptError(
                "`engine.revision_sequence` must be a positive integer"
            )
        recorded_engine = _required_sha256(engine, "engine_tree_sha256")
        recorded_protocol = _required_sha256(
            engine, "formalization_review_protocol_sha256"
        )
        try:
            ledger = validated_runtime_engine_revision_ledger(root)
        except EngineRevisionError as exc:
            raise FinalClosureReceiptError(
                "formalization engine registration is unavailable: " + str(exc)
            ) from exc
        revisions = ledger.get("revisions") if isinstance(ledger, Mapping) else None
        if not isinstance(revisions, list):
            raise FinalClosureReceiptError(
                "receipt engine revision is absent from registered history"
            )
        matching_revisions = [
            revision
            for revision in revisions
            if isinstance(revision, Mapping)
            and revision.get("engine_tree_sha256") == recorded_engine
            and revision.get("formalization_review_protocol_sha256")
            == recorded_protocol
        ]
        if len(matching_revisions) != 1:
            raise FinalClosureReceiptError(
                "receipt engine revision does not match registered history"
            )
        # Engine coordinates authenticate which registered verifier issued the
        # receipt; they are provenance, not a paper-evidence freshness key.
        # Currentness is checked below against the current protocol and every
        # receipt-bound source, Spec/proof closure, review, and build identity.
        # The display sequence may therefore be renumbered when branch ledgers
        # are linearized, and later engine revisions do not create pairwise
        # compatibility obligations for already-closed papers.

    paper_dir = root / "papers" / paper
    map_path = paper_dir / "audit" / "paper_statement_map.json"
    map_pin = _mapping(payload, "statement_map")
    _expect_exact_keys(map_pin, field="statement_map", required={"path", "sha256"})
    expected_map_path = map_path.relative_to(root).as_posix()
    if _required_string(map_pin, "path") != expected_map_path:
        raise FinalClosureReceiptError(
            f"`statement_map.path` must be `{expected_map_path}`"
        )
    _validate_file_pin(
        root,
        paper,
        payload,
        field="statement_map",
        expected_path=map_path,
        paper_local=False,
    )
    try:
        source_map = json.loads(map_path.read_text(encoding="utf-8"))
    except (OSError, UnicodeError, json.JSONDecodeError) as exc:
        raise FinalClosureReceiptError(f"current statement map is unreadable: {exc}") from exc
    if not isinstance(source_map, Mapping):
        raise FinalClosureReceiptError("current statement map must be an object")
    archive_surface_issues = source_archive_surface_validation_issues(
        paper_dir,
        source_map,
        repository_root=root,
        require_source_bytes=not allow_missing_source_bytes,
    )
    if archive_surface_issues:
        raise FinalClosureReceiptError(
            "current archive-source provenance is invalid: "
            + "; ".join(issue.message for issue in archive_surface_issues)
        )
    source_relative = _required_string(source_map, "source_artifact_path")
    expected_source = _source_artifact_path_from_map(root, paper, source_relative)
    source_pin = _mapping(payload, "source_artifact")
    _expect_exact_keys(source_pin, field="source_artifact", required={"path", "sha256"})
    source_pin = _mapping(payload, "source_artifact")
    _expect_exact_keys(source_pin, field="source_artifact", required={"path", "sha256"})
    source_path = _repository_path(
        root, _required_string(source_pin, "path"), field="source_artifact"
    )
    if source_path.resolve(strict=False) != expected_source.resolve(strict=False):
        raise FinalClosureReceiptError(
            "`source_artifact.path` must be "
            f"`{expected_source.relative_to(root).as_posix()}`"
        )
    map_source_hash = _required_sha256(source_map, "source_artifact_sha256")
    receipt_source_hash = _required_sha256(source_pin, "sha256")
    if receipt_source_hash != map_source_hash:
        raise FinalClosureReceiptError(
            "source-artifact pin does not agree with current paper_statement_map.json"
        )
    if source_path.exists():
        if not source_path.is_file() or _sha256_file(source_path) != map_source_hash:
            raise FinalClosureReceiptError(
                "source-artifact pin does not agree with current paper_statement_map.json"
            )
    elif not allow_missing_source_bytes:
        raise FinalClosureReceiptError(
            f"could not read `{source_path}`: canonical source bytes are unavailable"
        )

    # A stale protocol pin is already conclusive negative evidence: no Lean
    # closure result can make this receipt current.  Check it after the cheap
    # source pins but before launching the transitive Lean closure.  A matching
    # pin grants no credit and the validator still checks every Lean, review,
    # build, and date obligation below.
    protocol = _mapping(payload, "protocol")
    _expect_exact_keys(
        protocol,
        field="protocol",
        required={"formalization_review_protocol_sha256"},
    )
    if _required_sha256(protocol, "formalization_review_protocol_sha256") != (
        formalization_review_protocol_digest()
    ):
        raise FinalClosureReceiptError("formalization review protocol digest is stale")

    closure = _mapping(payload, "paper_interface_closure")
    _expect_exact_keys(closure, field="paper_interface_closure", required={"root", "sha256"})
    if _required_string(closure, "root") != "PaperInterface.lean":
        raise FinalClosureReceiptError(
            "`paper_interface_closure.root` must be `PaperInterface.lean`"
        )
    expected_closure_identity = _required_sha256(closure, "sha256")
    if expected_closure_identity != _current_interface_closure(
        root,
        paper,
        closure_provider_factory=closure_provider_factory,
        expected_identity=expected_closure_identity,
    ):
        raise FinalClosureReceiptError(
            "PaperInterface transitive import-closure SHA-256 is stale"
        )

    ledger_path = _validate_review_ledger_pin(root, paper, payload)

    focused_build = _mapping(payload, "focused_build")
    _expect_exact_keys(
        focused_build, field="focused_build", required={"command", "target", "result", "commit"}
    )
    status_path = paper_dir / "status.json"
    try:
        status = json.loads(status_path.read_text(encoding="utf-8"))
    except (OSError, UnicodeError, json.JSONDecodeError) as exc:
        raise FinalClosureReceiptError(f"current status file is unreadable: {exc}") from exc
    expected_command = _required_string(status, "build_target")
    if (
        lane == DIRECT_SOURCE_ROW_REVIEW_LANE
        and _status_requires_v11_source_spec_screening(status)
        and ledger_path.resolve() != (paper_dir / V11_SCREENING_LEDGER_RELATIVE).resolve()
    ):
        raise FinalClosureReceiptError(
            "a v11 source-spec closeout using direct-source-row-review must bind "
            f"`{V11_SCREENING_LEDGER_RELATIVE.as_posix()}` as its review ledger"
        )
    if _required_string(focused_build, "command") != expected_command:
        raise FinalClosureReceiptError(
            "focused build command does not match current status build_target"
        )
    if _required_string(focused_build, "target") != paper:
        raise FinalClosureReceiptError("focused build target does not match the paper")
    if _required_string(focused_build, "result") != "passed":
        raise FinalClosureReceiptError("focused build result must be `passed`")
    commit = _required_string(focused_build, "commit").lower()
    if not GIT_COMMIT_RE.fullmatch(commit):
        raise FinalClosureReceiptError("focused build commit must be a lowercase Git commit")
    if schema == RECEIPT_SCHEMA:
        build_receipt_path = _validate_file_pin(
            root,
            paper,
            payload,
            field="focused_build_receipt",
            expected_path=focused_build_receipt_path(root, paper),
            paper_local=False,
        )
        if build_receipt_path != focused_build_receipt_path(root, paper):
            raise FinalClosureReceiptError("focused build receipt path is invalid")
        build_receipt = validate_focused_build_receipt(root, paper)
        if _required_string(build_receipt, "commit").lower() != commit:
            raise FinalClosureReceiptError(
                "focused build receipt commit disagrees with final receipt"
            )

    closed_at = _required_string(payload, "closed_at")
    try:
        date.fromisoformat(closed_at)
    except ValueError as exc:
        raise FinalClosureReceiptError("`closed_at` must be YYYY-MM-DD") from exc

    if lane == RAW_SOURCE_RECORD_LANE:
        _validate_file_pin(
            root,
            paper,
            payload,
            field="raw_source_record",
            expected_path=paper_dir / "audit" / "source_record_audit.json",
            paper_local=False,
        )
    return receipt


def final_closure_receipt_error(
    root: Path,
    paper: str,
    *,
    required_lane: str | None = None,
    allow_missing_source_bytes: bool = False,
) -> str:
    """Return one concise error instead of raising for audit-gate composition."""

    try:
        validate_final_closure_receipt(
            root,
            paper,
            required_lane=required_lane,
            allow_missing_source_bytes=allow_missing_source_bytes,
        )
    except FinalClosureReceiptError as exc:
        return str(exc)
    return ""


def direct_source_row_review_receipt_error(
    root: Path, paper: str, *, allow_missing_source_bytes: bool = False
) -> str:
    """Validate the explicit direct-review lane; never infer it from a report."""

    return final_closure_receipt_error(
        root,
        paper,
        required_lane=DIRECT_SOURCE_ROW_REVIEW_LANE,
        allow_missing_source_bytes=allow_missing_source_bytes,
    )


def record_lean_import_closure_receipt(root: Path, paper: str) -> Path:
    """Persist Lean's already-receipted closure without reopening the paper.

    A current ignored closeout plan may supply the Lean-emitted record. The
    final receipt's closure digest selects the only acceptable record, and the
    saved-closure validator rechecks every current source, module association,
    build control, external artifact, and end-of-transaction mutation guard.
    If no saved record is available, the same function obtains one live from
    Lean. This operation creates a portable validation carrier; it does not
    issue or alter semantic, build, or final-closure evidence.
    """

    closure_receipt = load_final_closure_receipt(root, paper)
    if closure_receipt.payload.get("schema") in OBLIGATION_RECEIPT_SCHEMAS:
        path = lean_import_closure_receipt_path(root, paper)
        if not path.is_file():
            raise FinalClosureReceiptError(
                "graph-native closure has no Lean import-closure carrier"
            )
        validate_final_closure_receipt(root, paper)
        return path
    expected = _required_sha256(
        _mapping(closure_receipt.payload, "paper_interface_closure"),
        "sha256",
    )
    current = _current_interface_closure(
        root,
        paper,
        expected_identity=expected,
        persist_saved_closure=True,
    )
    if current != expected:
        raise FinalClosureReceiptError(
            "current PaperInterface closure disagrees with the canonical receipt"
        )
    path = lean_import_closure_receipt_path(root, paper)
    if not path.is_file():
        raise FinalClosureReceiptError(
            "Lean import-closure receipt was not materialized"
        )
    validate_final_closure_receipt(root, paper)
    return path


def record_current_lean_import_closure_receipt(root: Path, paper: str) -> Path:
    """Materialize Lean's current closure before semantic review begins.

    This is a portable input carrier, never an acceptance credential.  It lets
    the v11 source/Spec and prerequisite gates consume Lean's exact module
    graph without depending on the legacy raw source-record artifact.  The
    final closeout still revalidates the same closure and every watched input.
    """

    if not PAPER_RE.fullmatch(paper):
        raise FinalClosureReceiptError("paper identifier is malformed")
    paper_target = root / "papers" / f"{paper}.lean"
    if not paper_target.is_file():
        raise FinalClosureReceiptError(
            f"missing paper build entrypoint `{paper_target.relative_to(root)}`"
        )
    interface = root / "papers" / paper / "PaperInterface.lean"
    if not interface.is_file():
        raise FinalClosureReceiptError(
            f"missing PaperInterface entrypoint `{interface.relative_to(root)}`"
        )
    # One portable carrier serves both the complete v11 claim graph and the
    # actual focused-build target. The paper root is the authority for the
    # imported interface layout: some papers keep Specs and proof endpoints in
    # one PaperInterface module, while others split a ProofInterface module.
    # Requiring a filename here would reject the former without adding any
    # proof or closure check; Lean's loaded-module graph below owns membership.
    entrypoint = paper_target.relative_to(root).as_posix()
    _current_interface_closure(
        root,
        paper,
        persist_saved_closure=True,
        entrypoint=entrypoint,
    )
    path = lean_import_closure_receipt_path(root, paper)
    try:
        payload = json.loads(path.read_text(encoding="utf-8"))
        validated_receipt = validated_lean_import_closure_receipt_payload(
            payload, paper=paper
        )
        raw_closure = validated_receipt.get("lean_import_closure")
        assert isinstance(raw_closure, Mapping)
        loaded_modules = raw_closure.get("lean_loaded_modules")
        required_modules = {f"{paper}.PaperInterface"}
        if not isinstance(loaded_modules, list) or not required_modules.issubset(
            {str(module) for module in loaded_modules}
        ):
            raise ValueError(
                "paper build closure does not load the configured PaperInterface"
            )
    except (OSError, UnicodeError, json.JSONDecodeError, ValueError) as exc:
        raise FinalClosureReceiptError(
            "current Lean import-closure carrier was not materialized correctly: "
            + str(exc)
        ) from exc
    return path


def _git_head(root: Path) -> str:
    result = subprocess.run(
        ["git", "rev-parse", "HEAD"],
        cwd=root,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        text=True,
        check=False,
    )
    head = result.stdout.strip().lower()
    if result.returncode != 0 or not GIT_COMMIT_RE.fullmatch(head):
        raise FinalClosureReceiptError(
            "could not determine the current Git commit for receipt issuance"
        )
    return head


def _focused_build(root: Path, command: str) -> None:
    try:
        argv = shlex.split(command)
    except ValueError as exc:
        raise FinalClosureReceiptError(f"focused build command cannot be parsed: {exc}") from exc
    if not argv:
        raise FinalClosureReceiptError("focused build command is empty")
    completed = subprocess.run(
        argv,
        cwd=root,
        check=False,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        text=True,
    )
    diagnostic_failure = lean_diagnostic_failure_reason(
        completed.stdout, completed.stderr
    )
    if completed.returncode != 0 or diagnostic_failure:
        reason = diagnostic_failure or f"exit code {completed.returncode}"
        excerpt = bounded_lean_diagnostic_excerpt(
            completed.stdout, completed.stderr
        )
        if excerpt:
            reason += f": {excerpt}"
        raise FinalClosureReceiptError(
            f"focused build failed with {reason}"
        )


def _current_focused_build_inputs(
    root: Path, paper: str
) -> tuple[Mapping[str, Any], Mapping[str, Any], Path, Path, Path, Path]:
    """Return the legacy schema-1 whole-file focused-build inputs."""

    paper_dir = root / "papers" / paper
    status_path = paper_dir / "status.json"
    map_path = paper_dir / "audit" / "paper_statement_map.json"
    interface_path = paper_dir / "PaperInterface.lean"
    try:
        status = json.loads(status_path.read_text(encoding="utf-8"))
        source_map = json.loads(map_path.read_text(encoding="utf-8"))
    except (OSError, UnicodeError, json.JSONDecodeError) as exc:
        raise FinalClosureReceiptError(
            f"cannot read focused-build inputs: {exc}"
        ) from exc
    if not isinstance(status, Mapping) or not isinstance(source_map, Mapping):
        raise FinalClosureReceiptError("focused-build inputs must be JSON objects")
    source_relative = _required_string(source_map, "source_artifact_path")
    source_path = _source_artifact_path_from_map(root, paper, source_relative)
    if not interface_path.is_file():
        raise FinalClosureReceiptError("PaperInterface.lean is unavailable")
    return status, source_map, source_path, status_path, map_path, interface_path


def _current_focused_build_status(
    root: Path, paper: str
) -> tuple[Mapping[str, Any], Path]:
    """Return the command authority without coupling a build to audit files."""

    status_path = root / "papers" / paper / "status.json"
    try:
        status = json.loads(status_path.read_text(encoding="utf-8"))
    except (OSError, UnicodeError, json.JSONDecodeError) as exc:
        raise FinalClosureReceiptError(
            f"cannot read focused-build status: {exc}"
        ) from exc
    if not isinstance(status, Mapping):
        raise FinalClosureReceiptError("focused-build status must be a JSON object")
    return status, status_path


def record_focused_build_receipt(
    root: Path,
    paper: str,
    *,
    run_build: bool = True,
    persist_saved_closure: bool = True,
    authenticated_lean_import_closure_receipt: Mapping[str, Any] | None = None,
) -> Path:
    """Preserve a reusable, input-pinned focused-build result.

    This is operational evidence only.  The canonical final-closeout authority
    remains ``FINAL_CLOSURE_RECEIPT.md``; it can reuse this record only while
    its build command and exact transitive Lean entrypoint closure are still
    current. Source-review, map, ledger, and protocol authority remain
    independently bound by the canonical receipt and semantic gates. The
    ordinary CLI path runs the build here. The strict closeout orchestrator may
    set ``run_build=False`` only after authenticating the current
    ``focused_build`` stage receipt produced inside the frozen strict
    transaction; that path avoids compiling the same paper twice.
    """

    status, _status_path = _current_focused_build_status(root, paper)
    command = _required_string(status, "build_target")
    if run_build:
        _focused_build(root, command)
    payload: dict[str, Any] = {
        "paper": paper,
        "command": command,
        "target": paper,
        "result": "passed",
        "commit": _git_head(root),
    }
    if authenticated_lean_import_closure_receipt is None:
        interface_closure_sha256 = _current_interface_closure(
            root,
            paper,
            persist_saved_closure=persist_saved_closure,
        )
        payload.update(
            {
                "schema": FOCUSED_BUILD_RECEIPT_SCHEMA,
                "paper_interface_closure_sha256": interface_closure_sha256,
            }
        )
    else:
        if not is_exact_portable_paper_build_command(command, paper):
            raise FinalClosureReceiptError(
                "focused build target must be the exact portable paper-root target"
            )
        try:
            closure_receipt = validated_lean_import_closure_receipt_payload(
                authenticated_lean_import_closure_receipt,
                paper=paper,
            )
            closure = validated_lean_import_closure_payload(
                closure_receipt.get("lean_import_closure")
            )
        except ValueError as exc:
            raise FinalClosureReceiptError(
                "authenticated Lean import-closure receipt is malformed: "
                + str(exc)
            ) from exc
        closure_sha256 = lean_import_closure_payload_sha256(closure)
        if closure_receipt.get("lean_import_closure_sha256") != closure_sha256:
            raise FinalClosureReceiptError(
                "authenticated Lean import-closure receipt identity is stale"
            )
        payload.update(
            {
                "schema": AUTHENTICATED_CLOSURE_FOCUSED_BUILD_RECEIPT_SCHEMA,
                "lean_entrypoint": str(closure["entrypoint"]),
                "lean_import_closure_sha256": closure_sha256,
            }
        )
    path = focused_build_receipt_path(root, paper)
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(
        json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8"
    )
    validate_focused_build_receipt(
        root,
        paper,
        require_current_head=True,
        authenticated_lean_import_closure_receipt=(
            authenticated_lean_import_closure_receipt
        ),
    )
    return path


def validate_focused_build_receipt(
    root: Path,
    paper: str,
    *,
    require_current_head: bool = False,
    authenticated_lean_import_closure_receipt: Mapping[str, Any] | None = None,
) -> Mapping[str, Any]:
    """Check a recorded focused build without treating it as final closure."""

    path = focused_build_receipt_path(root, paper)
    try:
        payload = json.loads(path.read_text(encoding="utf-8"))
    except (OSError, UnicodeError, json.JSONDecodeError) as exc:
        raise FinalClosureReceiptError(
            f"could not read focused build receipt: {exc}"
        ) from exc
    common_required = {
        "schema",
        "paper",
        "command",
        "target",
        "result",
        "commit",
    }
    if not isinstance(payload, Mapping):
        raise FinalClosureReceiptError("focused build receipt fields are malformed")
    schema = payload.get("schema")
    if schema not in LEGACY_FOCUSED_BUILD_RECEIPT_SCHEMAS:
        raise FinalClosureReceiptError("focused build receipt schema is unsupported")
    if schema == 1:
        schema_required = {
            "status_sha256",
            "statement_map_sha256",
            "source_artifact_sha256",
            "paper_interface_sha256",
            "formalization_review_protocol_sha256",
        }
    elif schema == FOCUSED_BUILD_RECEIPT_SCHEMA:
        schema_required = {
            "paper_interface_closure_sha256",
        }
    else:
        schema_required = {
            "lean_entrypoint",
            "lean_import_closure_sha256",
        }
    if set(payload) != common_required | schema_required:
        raise FinalClosureReceiptError("focused build receipt fields are malformed")
    if _required_string(payload, "paper") != paper:
        raise FinalClosureReceiptError("focused build receipt paper does not match")
    status, _status_path = _current_focused_build_status(root, paper)
    if _required_string(payload, "command") != _required_string(status, "build_target"):
        raise FinalClosureReceiptError("focused build receipt command is stale")
    if _required_string(payload, "target") != paper:
        raise FinalClosureReceiptError("focused build receipt target is stale")
    if _required_string(payload, "result") != "passed":
        raise FinalClosureReceiptError("focused build receipt did not pass")
    commit = _required_string(payload, "commit").lower()
    if not GIT_COMMIT_RE.fullmatch(commit):
        raise FinalClosureReceiptError("focused build receipt commit is malformed")
    if require_current_head and commit != _git_head(root):
        raise FinalClosureReceiptError(
            "focused build receipt was issued for a different Git commit"
        )
    expected_pins: dict[str, Path] = {}
    if schema == 1:
        (
            _legacy_status,
            _source_map,
            source_path,
            legacy_status_path,
            map_path,
            interface_path,
        ) = _current_focused_build_inputs(root, paper)
        expected_pins.update(
            {
                "status_sha256": legacy_status_path,
                "statement_map_sha256": map_path,
                "source_artifact_sha256": source_path,
                "paper_interface_sha256": interface_path,
            }
        )
    elif schema == FOCUSED_BUILD_RECEIPT_SCHEMA:
        expected_closure = _required_sha256(
            payload, "paper_interface_closure_sha256"
        )
        if _current_interface_closure(
            root,
            paper,
            expected_identity=expected_closure,
        ) != expected_closure:
            raise FinalClosureReceiptError(
                "focused build receipt `paper_interface_closure_sha256` is stale"
            )
    else:
        try:
            if authenticated_lean_import_closure_receipt is None:
                closure_path = lean_import_closure_receipt_path(root, paper)
                raw_closure_receipt = json.loads(
                    closure_path.read_text(encoding="utf-8")
                )
            else:
                raw_closure_receipt = authenticated_lean_import_closure_receipt
            closure_receipt = validated_lean_import_closure_receipt_payload(
                raw_closure_receipt,
                paper=paper,
            )
            closure = validated_lean_import_closure_payload(
                closure_receipt.get("lean_import_closure")
            )
        except (OSError, UnicodeError, json.JSONDecodeError, ValueError) as exc:
            raise FinalClosureReceiptError(
                "current Lean import-closure receipt is invalid: " + str(exc)
            ) from exc
        expected_closure = _required_sha256(
            payload, "lean_import_closure_sha256"
        )
        if (
            closure_receipt.get("lean_import_closure_sha256") != expected_closure
            or lean_import_closure_payload_sha256(closure) != expected_closure
            or _required_string(payload, "lean_entrypoint")
            != str(closure["entrypoint"])
        ):
            raise FinalClosureReceiptError(
                "focused build receipt Lean import closure is stale"
            )
    for field, current_path in expected_pins.items():
        if _required_sha256(payload, field) != _sha256_file(current_path):
            raise FinalClosureReceiptError(f"focused build receipt `{field}` is stale")
    if schema == 1 and _required_sha256(
        payload, "formalization_review_protocol_sha256"
    ) != formalization_review_protocol_digest():
        raise FinalClosureReceiptError("focused build receipt protocol is stale")
    return payload


def _status_requires_v11_source_spec_screening(status: Mapping[str, Any]) -> bool:
    return explicit_raw_source_spec_screening_requested(status)


def _parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--paper")
    parser.add_argument("--check", action="store_true")
    parser.add_argument(
        "--diagnose-import-closure-accelerators",
        action="store_true",
        help=(
            "compare one paper's, or every checked-in paper's, non-accepting "
            "portable import-closure carrier with current repository inputs; "
            "never invoke semantic recovery or grant closure; exit zero means "
            "the diagnostic completed, not that every carrier matched"
        ),
    )
    parser.add_argument(
        "--record-focused-build",
        action="store_true",
        help=(
            "run the focused build and write its input-pinned operational receipt; "
            "the canonical final closure receipt may reuse it at the same commit"
        ),
    )
    parser.add_argument(
        "--record-lean-import-closure",
        action="store_true",
        help=(
            "persist Lean's canonical transitive import-closure record for "
            "fast path-independent validation of an already-current receipt"
        ),
    )
    parser.add_argument(
        "--record-current-lean-import-closure",
        action="store_true",
        help=(
            "ask Lean for the current transitive PaperInterface closure and "
            "write its non-accepting portable carrier before v11 review"
        ),
    )
    parser.add_argument("--allow-missing-source-bytes", action="store_true")
    return parser


def main(argv: list[str] | None = None) -> int:
    args = _parser().parse_args(argv)
    selected_actions = sum(
        bool(value)
        for value in (
            args.check,
            args.diagnose_import_closure_accelerators,
            args.record_focused_build,
            args.record_lean_import_closure,
            args.record_current_lean_import_closure,
        )
    )
    if selected_actions != 1:
        raise SystemExit(
            "choose exactly one of --check, "
            "--diagnose-import-closure-accelerators, --record-focused-build, "
            "--record-lean-import-closure, or "
            "--record-current-lean-import-closure"
        )
    if not args.diagnose_import_closure_accelerators and not args.paper:
        raise SystemExit("--paper is required for this action")
    if args.allow_missing_source_bytes and not args.check:
        raise SystemExit(
            "--allow-missing-source-bytes is valid only with --check"
        )
    try:
        if args.diagnose_import_closure_accelerators:
            print(
                json.dumps(
                    diagnose_import_closure_accelerators(
                        ROOT,
                        paper=args.paper,
                    ),
                    ensure_ascii=True,
                    indent=2,
                    sort_keys=True,
                )
            )
        elif args.record_current_lean_import_closure:
            path = record_current_lean_import_closure_receipt(ROOT, args.paper)
            print(f"wrote {path.relative_to(ROOT)}")
        elif args.record_lean_import_closure:
            path = record_lean_import_closure_receipt(ROOT, args.paper)
            print(f"wrote {path.relative_to(ROOT)}")
        elif args.record_focused_build:
            path = record_focused_build_receipt(ROOT, args.paper)
            print(f"wrote {path.relative_to(ROOT)}")
        else:
            current = validate_final_closure_receipt(
                ROOT,
                args.paper,
                allow_missing_source_bytes=args.allow_missing_source_bytes,
            )
            if current.terminal_validation_route == "lean_semantic_recovery":
                detail = (
                    f" ({current.terminal_validation_detail})"
                    if current.terminal_validation_detail
                    else ""
                )
                print(
                    "final closure receipt is current via Lean semantic "
                    f"recovery after import-container drift: {args.paper}{detail}"
                )
            else:
                print(f"final closure receipt is current: {args.paper}")
    except FinalClosureReceiptError as exc:
        print(f"final-closure-receipt: {exc}", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":  # pragma: no cover - CLI wrapper.
    raise SystemExit(main())
