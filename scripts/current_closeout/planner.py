#!/usr/bin/env python3
"""Plan current paper closeout from validated typed facts.

The planner checks terminal accepted-graph currentness first. For an unclosed
paper it validates deterministic intake and route structure, acquires one
current-v11 evidence transaction, and passes those facts to the closed v11
reducer. Presentation caches, historical source-record transitions, and legacy
semantic sidecars are not planner authorities.

The resulting schedule is non-accepting. Final acceptance still requires the
strict paper transaction, focused build, plan-bound adversarial source review,
and publication of the accepted obligation graph.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import re
import shlex
import sys
from collections.abc import Iterable, Mapping
from dataclasses import dataclass
from pathlib import Path
from typing import TYPE_CHECKING, Any

ROOT = Path(__file__).resolve().parents[2]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

if TYPE_CHECKING:
    from scripts import lean_signature_manifest as lean_manifest
from scripts.check_formalization_engine_revision import (
    runtime_engine_registration_error,
)
from scripts.closeout_document_gates import (
    closeout_document_hard_errors,
    final_holistic_audit_hard_errors,
)
from scripts.closeout_execution_state import (
    closeout_worker_state_path as canonical_closeout_worker_state_path,
)
from scripts.closeout_execution_state import (
    default_closeout_execution_path,
    effective_closeout_execution_state,
    resolve_paper_folder,
    running_execution_summary,
)
from scripts.closeout_intake_freeze import source_intake_readiness
from scripts.closeout_plan_receipt import (
    OPERATIONAL_PLAN_IDENTITY_SCHEMA,
    CloseoutPlanReceiptError,
    build_lean_closure_operational_projection,
    closeout_plan_receipt_path,
    content_input_snapshot,
    resolved_plan_final_holistic_audit_surface,
)
from scripts.closeout_status_projection import (
    CloseoutStatusProjectionError,
    paper_status_acceptance_projection,
    paper_status_acceptance_projection_from_payload,
)
from scripts.current_closeout.actions import (
    classify_v11_worker_disposition,
    schedule_v11_closeout,
)
from scripts.current_closeout.approved_contexts import (
    current_approved_review_context_projection,
    expected_approved_review_context_projection,
)
from scripts.current_closeout.graph_preparation import (
    persist_retained_v11_lean_review_graph,
    prepare_v11_lean_review_graph,
)
from scripts.current_closeout.lean_review_graph import (
    V11_LEAN_CLAIM_GRAPH_EVIDENCE_LANE,
    builder_issued_v11_lean_operational_provider,
    builder_issued_v11_lean_review_graph_carrier,
)
from scripts.current_closeout.plan_publication import (
    CloseoutPlanPublicationInputs,
    CloseoutPlanReceiptPublication,
    CurrentV11OperationalPlan,
    closeout_plan_input_paths,
    publication_input_identity,
    publish_closeout_plan_receipt,
)
from scripts.current_closeout.plan_publication import (
    stat_identity as _stat_identity,
)
from scripts.current_closeout.protocol_selection import current_v11_protocol_selected
from scripts.current_closeout.reducer import (
    V11CloseoutState,
    V11WorkerDisposition,
)
from scripts.current_closeout.review_surface import (
    load_current_v11_review_graph_projection,
)
from scripts.current_closeout.strict_transaction import (
    STRICT_CLOSEOUT_EXECUTION_STAGES,
    current_closeout_execution_projection,
)
from scripts.evidence_run_context import V11EvidenceRunContext
from scripts.final_closure_receipt import (
    FinalClosureReceiptError,
    load_final_closure_receipt,
    validate_final_closure_receipt,
)
from scripts.final_holistic_audit_surface import (
    FinalHolisticAuditSurfaceError,
    build_final_holistic_audit_surface_from_repository,
)
from scripts.final_validation_report_status import report_status_alignment_errors
from scripts.obligation_preflight import structural_obligation_preflight
from scripts.source_coverage_scope import (
    DEEP_PAPER_WITH_ALL_PROSE_CLAIMS,
    source_coverage_mode_from_map,
    source_item_is_named_theoretical_statement,
    source_named_result_environment_kinds_from_map,
)
from scripts.v11_screening_contract import validate_v11_screening_container

SHA256_RE = re.compile(r"^[0-9a-f]{64}$")


def _raw_source_spec_screening_requested(
    folder: Path,
    status_payload: object,
    source_map_payload: object | None = None,
) -> bool:
    """Use the accepting gate's single v11 protocol-selection predicate."""

    del folder  # Routing is not semantic protocol identity.
    return current_v11_protocol_selected(status_payload, source_map_payload)


# These are the declared dispositions for which the graph-native machinery can
# close the *reviewed scope*.  This is intentionally broader than
# ``FULL_CLOSEOUT_STATUSES``: an honestly partially formalized paper still
# needs one current source/Spec, Lean, and evidence closure that records its
# exact external boundary.  The full-status validators remain responsible for
# refusing to credit that closed partial boundary as a full formalization.
#
# A planner must not schedule a strict acceptance route for an unrecognized
# status that merely happens to begin with a favorable word.
CLOSEOUT_PLANNER_ELIGIBLE_STATUSES = frozenset(
    {"formalized", "formalized with caveat", "partially formalized"}
)
V11_SOURCE_SPEC_SEMANTIC_LANE = "current_v11_raw_source_to_expanded_spec"


def current_v11_direct_semantic_review_state(*args: object, **kwargs: object):
    """Load the current semantic verdict only after v11 planning is selected."""

    from scripts.current_closeout.semantic_review import (
        current_v11_direct_semantic_review_state as evaluate,
    )

    return evaluate(*args, **kwargs)


def current_v11_raw_source_spec_screening_findings(
    *args: object,
    **kwargs: object,
):
    """Load current screening validation only on its repair branch."""

    from scripts.current_closeout.semantic_review import (
        current_v11_raw_source_spec_screening_findings as evaluate,
    )

    return evaluate(*args, **kwargs)


def current_graph_realization_preflight(
    folder: Path,
    *,
    evidence_context: object | None = None,
) -> dict[str, Any]:
    """Validate current realization from the retained v11 graph only.

    The planner has already selected and validated the current graph-native
    protocol before reaching this seam.  A missing graph is therefore a hard
    repair obligation, never permission to consult or rewrite a historical
    persisted source-correspondence worksheet.
    """

    from scripts.current_closeout.realization import (
        current_graph_realization_preflight as preflight,
    )

    blocked = {
        "schema": 3,
        "required": True,
        "state": "blocked",
        "current": False,
        "graph_native_items": [],
        "errors": ["current v11 realization graph is unavailable"],
        "acceptance_credential": False,
    }
    if (
        evidence_context is None
        or getattr(evidence_context, "source_semantic_lane", "")
        != V11_LEAN_CLAIM_GRAPH_EVIDENCE_LANE
    ):
        return blocked
    source_map = getattr(evidence_context, "statement_map", None)
    if not isinstance(source_map, Mapping):
        return {**blocked, "errors": ["current v11 statement map is unavailable"]}
    try:
        carrier = builder_issued_v11_lean_review_graph_carrier(
            folder,
            evidence_context,
            repository_root=ROOT,
        )
    except (OSError, RuntimeError, TypeError, ValueError) as exc:
        return {
            **blocked,
            "errors": ["current v11 realization graph is unavailable: " + str(exc)],
        }
    return preflight(
        paper=folder.name,
        source_map=source_map,
        graph_carrier=carrier,
    )


def closeout_worker_state_path(paper: str) -> Path:
    return canonical_closeout_worker_state_path(ROOT, paper)


def _root_import_closure_mutation_snapshots(
    root: Path,
    folder: Path,
    provider: lean_manifest.RepositoryBuildInputSnapshotProvider,
) -> tuple[
    dict[str, tuple[int, int, int, int, int] | None],
    dict[str, tuple[int, int, int, int, int] | None],
    list[str],
    dict[str, object] | None,
]:
    """Capture the exact Lean-selected paper-root source/compiled closure."""

    source_records = provider.repository_source_snapshot(folder.name)
    if not source_records:
        return (
            {},
            {},
            [
                "Lean could not provide the exact paper-root import closure; "
                "run the planner's focused build action before replanning"
            ],
            None,
        )
    closure_receipt = provider.lean_import_closure_receipt(folder.name)
    if closure_receipt is None:
        return (
            {},
            {},
            ["Lean did not retain a validated paper-root loaded-module receipt"],
            None,
        )
    source_snapshot: dict[str, tuple[int, int, int, int, int] | None] = {}
    # A cached ``.olean`` is neither source evidence nor a stable operational
    # input.  In particular, a legitimate worktree-local build cache can use
    # a symlink to a shared cache or another checkout.  Binding that resolved
    # path would make planning machine- and worktree-dependent, while binding
    # its bytes would still add no assurance: the strict worker performs the
    # authoritative focused Lean build after it freezes the source closure.
    #
    # Keep this mutation lane source-only.  The Lean-owned closure receipt and
    # its external-artifact identity already protect the current elaboration
    # environment; the final build establishes the proof result.
    compiled_snapshot: dict[str, tuple[int, int, int, int, int] | None] = {}
    errors: list[str] = []
    for module, path, _content, _digest_value in source_records:
        try:
            source_snapshot[str(path.resolve())] = _stat_identity(path.stat())
        except OSError as exc:
            source_snapshot[str(path.resolve())] = None
            errors.append(f"paper-root Lean source is unavailable: {path}: {exc}")
    return source_snapshot, compiled_snapshot, errors, closure_receipt


def _strict_transaction_content_snapshot(
    folder: Path,
    *,
    evidence_context: V11EvidenceRunContext,
) -> tuple[dict[str, dict[str, Any]] | None, str]:
    """Freeze exactly the selected current-v11 transaction inputs once.

    Historical raw receipts and their producer-watch expansion are not a
    planner lane.  An unclosed historical paper is routed to the current
    protocol before this function is reachable.  Requiring the nominal,
    builder-issued v11 context makes a legacy fallback structurally
    unrepresentable while retaining byte and acceptance-status mutation
    checks for every selected current input.
    """

    try:
        context = evidence_context
        if not isinstance(context, V11EvidenceRunContext):
            raise ValueError(
                "strict plan input inventory requires a nominal v11 evidence context"
            )
        if not context.issued_by_builder:
            raise ValueError(
                "strict plan input inventory requires a builder-issued v11 context"
            )
        if context.folder != folder.resolve():
            raise ValueError(
                "strict plan input inventory received a context for another paper"
            )
        projected_controls = {
            (ROOT / "papers" / "audit_config.json").resolve(),
            (ROOT / "lakefile.toml").resolve(),
            (
                ROOT / "scripts" / "refresh_validation_report_audit_summaries.py"
            ).resolve(),
        }
        selected_context_snapshots: dict[Path, object] = {}
        for snapshot in context.input_snapshots:
            path = getattr(snapshot, "path", None)
            if not isinstance(path, Path):
                raise ValueError("evidence transaction has a malformed input path")
            resolved = path.resolve()
            if (
                resolved in projected_controls
                or resolved == (folder / "status.json").resolve()
            ):
                continue
            if not hasattr(snapshot, "sha256"):
                raise ValueError(
                    "evidence transaction has a malformed exact input identity"
                )
            expected_sha256 = snapshot.sha256
            if (
                expected_sha256 is not None
                and not SHA256_RE.fullmatch(str(expected_sha256))
            ):
                raise ValueError(
                    "evidence transaction has a malformed exact input identity"
                )
            selected_context_snapshots[path] = snapshot
        paths = set(selected_context_snapshots)
        current_snapshot = content_input_snapshot(ROOT, paths)
        changed: list[str] = []
        for path, frozen in selected_context_snapshots.items():
            try:
                relative = path.relative_to(ROOT).as_posix()
            except ValueError as exc:
                raise ValueError(
                    "evidence transaction input is outside the repository"
                ) from exc
            current = current_snapshot.get(relative)
            if (
                not isinstance(current, Mapping)
                or current.get("sha256") != frozen.sha256
            ):
                changed.append(relative)
        if changed:
            return None, (
                "evidence transaction input changed before closeout plan freeze: "
                + ", ".join(changed[:5])
                + ("; ..." if len(changed) > 5 else "")
            )
        expected_status = paper_status_acceptance_projection_from_payload(
            folder.name,
            context.status_payload,
        )
        if paper_status_acceptance_projection(ROOT, folder.name) != expected_status:
            return None, (
                "paper status acceptance configuration changed before closeout "
                "plan freeze"
            )
        return current_snapshot, ""
    except (CloseoutPlanReceiptError, OSError, RuntimeError, ValueError) as exc:
        return None, f"could not acquire strict closeout input inventory: {exc}"














def _static_closeout_document_hard_errors(
    folder: Path, status_payload: Mapping[str, Any] | None
) -> list[tuple[Path, str]]:
    """Mirror current document ERRORs without paying for the intake scan.

    Historical accepted graphs return before prospective planning, and an
    unclosed historical paper receives a migration action.  This current-path
    helper therefore never consults the retired corrected-scope evidence lane.
    The plan-bound final adversarial review remains downstream of the frozen
    semantic and Lean identities.
    """

    final_holistic_required = _raw_source_spec_screening_requested(
        folder, status_payload
    )
    return [
        (error.path, error.message)
        for error in closeout_document_hard_errors(
            folder,
            corrected_scope_current=False,
            final_holistic_required=final_holistic_required,
            check_final_holistic=not final_holistic_required,
        )
    ]


def _planner_path(path: Path) -> str:
    """Render repository-relative paths while keeping isolated fixtures usable."""

    try:
        return path.relative_to(ROOT).as_posix()
    except ValueError:
        return str(path)


def _closeout_preflight_projection(errors: Iterable[str]) -> dict[str, Any]:
    """Expose only the blocking result; the strict worker owns full findings."""

    error_list = [str(error) for error in errors if str(error).strip()]
    return {
        "ready": not error_list,
        "state": "current" if not error_list else "blocked",
        "errors": error_list,
        "acceptance_credential": False,
    }


def _stop_for_closeout_preflight(
    plan: dict[str, Any],
    *,
    key: str,
    preflight: Mapping[str, Any],
    action_id: str,
    fallback_reason: str,
    **action_metadata: Any,
) -> bool:
    """Attach one deterministic repair action and report whether it blocks."""

    plan[key] = dict(preflight)
    if preflight.get("ready") is True:
        return False
    messages = [str(error).strip() for error in preflight.get("errors") or []]
    action = {
        "id": action_id,
        "state": "ready_now",
        "required": True,
        "reason": "; ".join(messages) or fallback_reason,
        "preserves_current_lean_graph": True,
        "preserves_current_semantic_review": True,
        **action_metadata,
    }
    plan.update(
        {
            "expensive_planning_deferred": True,
            "next_action": action,
            "actions": [action],
        }
    )
    return True


def _terminal_presentation_closeout_preflight(
    folder: Path,
    status_payload: object,
    *,
    all_selected_semantic_review_sha256: str | None = None,
) -> dict[str, Any]:
    """Require final human-facing products only after semantic/build stability."""

    required = (
        folder / "FINAL_VALIDATION_REPORT.md",
        folder / "docs" / "DependencyDAG.tex",
        folder / "docs" / "DependencyDAG.pdf",
        folder / "audit" / "human_review_packet_lean_cache.json",
        folder / "docs" / "HUMAN_REVIEW_PACKET.tex",
        folder / "docs" / "HUMAN_REVIEW_PACKET.pdf",
    )
    errors = [
        f"{_planner_path(path)}: missing terminal closeout presentation artifact"
        for path in required
        if not path.is_file()
    ]
    if not isinstance(status_payload, Mapping):
        errors.append(
            f"{_planner_path(folder / 'status.json')}: selected evidence context "
            "has no status payload for terminal document validation"
        )
    report = folder / "FINAL_VALIDATION_REPORT.md"
    if report.is_file() and isinstance(status_payload, Mapping):
        try:
            report_text = report.read_text(encoding="utf-8")
        except OSError as exc:
            errors.append(
                f"{_planner_path(report)}: final validation report is unreadable: {exc}"
            )
        else:
            errors.extend(
                f"{_planner_path(report)}: final validation report/status "
                f"alignment: {message}"
                for message in report_status_alignment_errors(
                    status_payload, report_text
                )
            )
    for document_error in closeout_document_hard_errors(
        folder,
        corrected_scope_current=False,
        final_holistic_required=True,
        check_final_holistic=False,
        require_visual_dag_inspection=True,
        all_selected_semantic_review_sha256=(
            all_selected_semantic_review_sha256
        ),
    ):
        rendered = f"{_planner_path(document_error.path)}: {document_error.message}"
        if rendered not in errors:
            errors.append(rendered)
    return _closeout_preflight_projection(errors)


def _named_support_triage_findings(
    source_map_payload: object, source_map_path: Path,
) -> list[dict[str, str]]:
    """Locate ambiguous dispositions without granting or denying coverage."""

    if not isinstance(source_map_payload, Mapping):
        return []
    items = source_map_payload.get("items")
    if not isinstance(items, Mapping):
        return []
    environment_kinds = source_named_result_environment_kinds_from_map(source_map_payload)
    findings = []
    for item_id, item in sorted(items.items()):
        if not isinstance(item, dict) or str(item.get("inventory_role") or "").strip() != "proof_support":
            continue
        if not source_item_is_named_theoretical_statement(
            item, declared_environment_kinds=environment_kinds,
        ):
            continue
        anchors = item.get("source_anchor_evidence")
        anchor_coordinates = [
            f"{str(anchor.get('path') or '')[:240]}:"
            f"{anchor.get('line_start')}-{anchor.get('line_end')}"
            for anchor in anchors if isinstance(anchor, Mapping)
        ] if isinstance(anchors, list) else []
        contract = item.get("semantic_contract")
        route_names = [str(contract[key]) for key in (
            "spec_declaration", "evidence_declaration",
        ) if isinstance(contract, Mapping) and key in contract]
        for key in ("lean_declarations", "support_lean_declarations", "current_lean_route"):
            values = item.get(key)
            if isinstance(values, list):
                route_names.extend(value for value in values if isinstance(value, str))
        atoms = item.get("source_claim_atoms")
        if isinstance(atoms, list):
            route_names.extend(
                atom["reviewed_lean_route"] for atom in atoms
                if isinstance(atom, Mapping) and isinstance(atom.get("reviewed_lean_route"), str)
            )
        findings.append({
            "severity": "WARN",
            "path": _planner_path(source_map_path),
            "message": (
                f"items.{item_id}: named source presentation has a proof_support disposition; "
                f"recorded source locators (first 3)={anchor_coordinates[:3]}; "
                f"own recorded route names (first 8)={[name[:160] for name in route_names[:8]]}. "
                "Reconcile as an independent claim requiring its own reviewed coverage, "
                "a source repetition/component, externally cited proof background, or an "
                "explicit partial boundary. These coordinates and routes are navigation, "
                "not validated coverage or an automatic exemption; source coverage and "
                "complete-scope review remain authoritative."
            ),
        })
    return findings


def static_closeout_readiness(
    folder: Path,
    *,
    include_intake: bool = True,
    require_terminal_documents: bool = True,
) -> dict[str, Any]:
    """Find deterministic paper-local blockers before any manifest hashing.

    This advisory preflight intentionally does not reproduce semantic audit
    logic. Unknown semantic lanes remain delegated to the authoritative strict
    closeout and never become acceptance evidence here.  ``include_intake``
    controls the prospective intake's exact source-artifact/atom scan: callers
    that only need metadata diagnostics can defer that byte-heavy work until a
    paper has passed the cheap status-eligibility gate.

    Final reports, DAGs, and their status prose are derived terminal products.
    ``require_terminal_documents=False`` reports that lane but does not let it
    block source intake, Lean graph acquisition, or semantic review.  The
    strict closeout transaction still requires and validates those products
    before acceptance.

    This function never opens or interprets Lean source. Declaration
    existence, review-surface membership, proof endpoints, placeholders,
    imports, and axiom closure belong to the typed Lean graph, Lean-owned
    module closure, and focused build. A cheap Python lexer cannot block those
    authorities or substitute for them.
    """

    evidence_required = [
        folder / "PaperInterface.lean",
        folder / "status.json",
        folder / "audit" / "paper_statement_map.json",
        ROOT / "papers" / f"{folder.name}.lean",
    ]
    terminal_required = [
        folder / "FINAL_VALIDATION_REPORT.md",
        folder / "docs" / "DependencyDAG.tex",
        folder / "docs" / "DependencyDAG.pdf",
    ]
    missing_evidence = [
        str(path.relative_to(ROOT))
        for path in evidence_required
        if not path.is_file()
    ]
    missing_terminal = [
        str(path.relative_to(ROOT))
        for path in terminal_required
        if not path.is_file()
    ]
    missing = [
        *missing_evidence,
        *(missing_terminal if require_terminal_documents else []),
    ]
    report_status_errors: tuple[str, ...] = ()
    status_payload: Mapping[str, Any] | None = None
    status_path = folder / "status.json"
    report_path = folder / "FINAL_VALIDATION_REPORT.md"
    if (
        require_terminal_documents
        and status_path.is_file()
        and report_path.is_file()
    ):
        try:
            decoded_status_payload = json.loads(status_path.read_text(encoding="utf-8"))
            report_text = report_path.read_text(encoding="utf-8")
        except (OSError, json.JSONDecodeError):
            # Status decoding itself is handled by the status preflight below;
            # this lane only owns a valid status/report contract mismatch.
            pass
        else:
            if isinstance(decoded_status_payload, Mapping):
                status_payload = decoded_status_payload
                report_status_errors = report_status_alignment_errors(
                    status_payload, report_text
                )

    if status_payload is None and status_path.is_file():
        try:
            decoded_status_payload = json.loads(status_path.read_text(encoding="utf-8"))
        except (OSError, json.JSONDecodeError):
            pass
        else:
            if isinstance(decoded_status_payload, Mapping):
                status_payload = decoded_status_payload

    build_target_errors: list[str] = []

    document_errors = (
        _static_closeout_document_hard_errors(folder, status_payload)
        if require_terminal_documents
        else []
    )
    status_route_projection_errors: tuple[str, ...] = ()
    source_map_payload: object | None = None
    source_map_path = folder / "audit" / "paper_statement_map.json"
    try:
        source_map_payload = json.loads(source_map_path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError):
        # Required-artifact and source-lane checks own unreadable-map errors.
        pass
    if status_payload is not None:
        if (
            isinstance(source_map_payload, Mapping)
            and source_map_payload.get("semantic_route_schema") == 2
        ):
            # The status surface is generated human-navigation metadata, not
            # an independent semantic gate.  Check it cheaply before the one
            # Lean graph is acquired so a final reader is never shown a stale
            # wrapper or misses the current typed route.
            from scripts.activate_v11_review_surface import (
                status_route_projection_errors as _status_route_projection_errors,
            )

            status_route_projection_errors = _status_route_projection_errors(
                status_payload,
                source_map_payload,
                paper=folder.name,
            )
        if _raw_source_spec_screening_requested(
            folder, status_payload, source_map_payload
        ):
            from scripts.paper_build_command import (
                is_exact_portable_paper_build_command,
            )

            if not is_exact_portable_paper_build_command(
                status_payload.get("build_target"), folder.name
            ):
                build_target_errors.append(
                    "build_target must be `lake build PAPER` or `lake build +PAPER`"
                )
    cheap_blockers = [
        *[f"missing required closeout artifact: {path}" for path in missing],
        *[
            "final validation report/status alignment: " + error
            for error in report_status_errors
        ],
        *[
            "closeout document: "
            + str(path.relative_to(ROOT))
            + ": "
            + message
            for path, message in document_errors
        ],
        *[
            "review-surface projection: " + error
            for error in status_route_projection_errors
        ],
        *["focused build target: " + error for error in build_target_errors],
    ]

    if include_intake and not cheap_blockers:
        intake = source_intake_readiness(folder, repository_root=ROOT)
    elif include_intake:
        intake = {
            "ready": None,
            "state": "deferred_due_to_static_blocker",
            "errors": [],
            "reason": (
                "exact source-artifact and atom validation is deferred until "
                "the listed cheap closeout blockers are resolved"
            ),
        }
    else:
        intake = {
            "ready": None,
            "state": "deferred_until_closeout_eligibility",
            "errors": [],
            "reason": (
                "exact source-artifact and atom validation is deferred until "
                "the paper is eligible for closeout"
            ),
        }
    blockers = [
        *cheap_blockers,
        *[
            f"source intake: {error}"
            for error in intake.get("errors", [])
            if include_intake
        ],
    ]
    return {
        "ready": not blockers,
        "acceptance_credential": False,
        "lanes": {
            "required_artifacts": {
                "ready": not missing_evidence,
                "missing": missing_evidence,
                "scope": "source, interface, status, and Lean entrypoint inputs",
            },
            "terminal_presentation_artifacts": {
                "ready": not missing_terminal,
                "missing": missing_terminal,
                "required_now": require_terminal_documents,
                "state": (
                    "current" if not missing_terminal
                    else (
                        "blocked" if require_terminal_documents
                        else "deferred_until_terminal_closeout"
                    )
                ),
                "scope": "final report and rendered dependency DAG",
            },
            "paper_local_proof_surface": {
                "ready": None,
                "state": "deferred_to_lean_graph_and_focused_build",
                "scope": "Lean-elaborated declaration, proof, and axiom closure",
                "python_lean_source_parsing": False,
            },
            "focused_build_target": {
                "ready": not build_target_errors,
                "errors": build_target_errors,
                "scope": "exact path-independent paper-root Lake target",
            },
            "final_validation_report_status": {
                "ready": (
                    not report_status_errors
                    if require_terminal_documents
                    else None
                ),
                "errors": list(report_status_errors),
                "state": (
                    "current"
                    if require_terminal_documents and not report_status_errors
                    else (
                        "blocked" if require_terminal_documents
                        else "deferred_until_terminal_closeout"
                    )
                ),
                "scope": "controlled Closeout Status/status.json agreement only",
            },
            "review_surface_projection": {
                "ready": not status_route_projection_errors,
                "errors": list(status_route_projection_errors),
                "scope": (
                    "generated status navigation projected from typed source "
                    "routes; not semantic or proof evidence"
                ),
            },
            "strict_closeout_documents": {
                "ready": not document_errors if require_terminal_documents else None,
                "errors": [
                    {
                        "path": str(path.relative_to(ROOT)),
                        "message": message,
                    }
                    for path, message in document_errors
                ],
                "state": (
                    "current"
                    if require_terminal_documents and not document_errors
                    else (
                        "blocked" if require_terminal_documents
                        else "deferred_until_terminal_closeout"
                    )
                ),
                "scope": "strict ERROR-class report and source-first audit gates",
            },
            "review_surface_structure": {
                "ready": None,
                "state": "deferred_to_typed_route_and_lean_graph_preflight",
                "errors": [],
                "findings": _named_support_triage_findings(
                    source_map_payload, source_map_path,
                ),
                "scope": (
                    "typed source/Spec/proof routes and Lean-elaborated declaration "
                    "membership"
                ),
                "python_lean_source_parsing": False,
            },
            "tracked_lean_import_closure": {
                "ready": None,
                "state": "deferred_to_lean_owned_import_closure",
                "errors": [],
                "scope": "Lean-loaded repository and external module closure",
                "python_lean_source_parsing": False,
            },
            "source_intake_boundary": intake,
            "semantic_and_recursive_gates": {
                "state": "deferred_to_authoritative_closeout",
                "proof_placeholder_scope": "exact Lean-loaded import closure",
                "reason": (
                    "the planner does not duplicate semantic receipt producers or "
                    "turn legacy missing fields into new closeout requirements"
                ),
            },
        },
        "blockers": blockers,
    }


def _paper_closeout_status_preflight(folder: Path) -> tuple[str, str]:
    """Return the declared status and a closeout-eligibility error, if any."""

    try:
        payload = json.loads((folder / "status.json").read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError) as exc:
        return "", f"paper-local status metadata is unavailable: {exc}"
    if not isinstance(payload, Mapping):
        return "", "paper-local status metadata is not an object"
    status = str(payload.get("status") or "").strip().lower()
    if not status:
        return "", "paper-local status metadata has no status"
    if status in CLOSEOUT_PLANNER_ELIGIBLE_STATUSES:
        return status, ""
    return (
        status,
        "paper is not eligible for graph-native closeout while its status is "
        f"`{status}`; select a recognized final disposition before running "
        "receipt or manifest work",
    )

def v11_structural_graph_input_preflight(
    folder: Path,
    *,
    require_prerequisite_ledger_bindings: bool = True,
) -> dict[str, Any] | None:
    """Return the complete cheap typed-route preflight before Lean acquisition.

    Every source atom, Spec/proof route, and semantic-prerequisite ledger must
    be structurally complete before the one Lean-owned graph is acquired. The
    graph-native realization is downstream, so this phase permits an absent
    correspondence record while still rejecting a malformed partial record.
    The source map may be absent only in isolated orchestration fixtures;
    production readiness rejects that case before this helper is reached.
    """

    statement_map = folder / "audit" / "paper_statement_map.json"
    if not statement_map.is_file():
        return None
    try:
        payload = json.loads(statement_map.read_text(encoding="utf-8"))
    except (OSError, UnicodeDecodeError, json.JSONDecodeError) as exc:
        return {
            "schema": 1,
            "acceptance_credential": False,
            "paper": folder.name,
            "current": False,
            "errors": [f"paper statement map is unreadable: {exc}"],
        }
    paper_prerequisite_path = folder / "audit" / "paper_semantic_prerequisites.json"
    library_review_path = folder / "audit" / "library_semantic_review.json"
    paper_prerequisites: object | None = None
    library_semantic_review: object | None = None
    if paper_prerequisite_path.is_file() and library_review_path.is_file():
        try:
            paper_prerequisites = json.loads(
                paper_prerequisite_path.read_text(encoding="utf-8")
            )
            library_semantic_review = json.loads(
                library_review_path.read_text(encoding="utf-8")
            )
        except (OSError, UnicodeDecodeError, json.JSONDecodeError) as exc:
            return {
                "schema": 1,
                "acceptance_credential": False,
                "paper": folder.name,
                "current": False,
                "errors": [f"semantic-prerequisite ledger is unreadable: {exc}"],
            }
    projection = structural_obligation_preflight(
        payload,
        paper=folder.name,
        paper_prerequisites=paper_prerequisites,
        library_semantic_review=library_semantic_review,
        require_theorem_endpoints=True,
        require_source_spec_correspondence=False,
        require_prerequisite_ledger_bindings=(
            require_prerequisite_ledger_bindings
        ),
    ).projection()
    # A current graph-native closeout has a source-boundary contract: every
    # source-facing definition/model/condition is explicitly routed to its
    # material paper or library declaration.  Historical maps without that
    # contract remain readable through their accepted historical receipts, but
    # must be migrated before this planner acquires a new graph or emits a
    # prerequisite-review queue.  Otherwise the legacy fallback would turn the
    # entire Lean closure into synthetic, source-less LLM obligations.
    if payload.get("semantic_route_schema") != 2:
        errors = [str(error) for error in projection.get("errors") or []]
        errors.append(
            "current graph-native closeout requires semantic_route_schema 2; "
            "migrate explicit source-semantic declaration routes before Lean "
            "graph acquisition or prerequisite review"
        )
        return {
            **projection,
            "acceptance_credential": False,
            "current": False,
            "errors": list(dict.fromkeys(errors)),
        }
    return projection


def _v11_lean_import_closure_current_error(
    folder: Path,
    payload: object,
) -> str:
    """Validate a saved closure against current exact repository inputs."""

    try:
        from scripts.lean_import_closure import (
            validated_lean_import_closure_receipt_payload,
        )
        from scripts.lean_signature_manifest import (
            RepositoryBuildInputSnapshotProvider,
        )

        receipt = validated_lean_import_closure_receipt_payload(
            payload,
            paper=folder.name,
        )
        closure = receipt.get("lean_import_closure")
        if not isinstance(closure, Mapping):
            raise ValueError("Lean import-closure receipt has no closure object")
        provider = RepositoryBuildInputSnapshotProvider(ROOT)
        if not provider.validated_repository_source_snapshot(closure):
            raise ValueError("Lean import closure has no current repository source")
    except (OSError, RuntimeError, TypeError, ValueError) as exc:
        return str(exc)
    return ""


def current_v11_source_spec_semantic_lane(
    folder: Path,
    *,
    source_map: Mapping[str, Any],
    evidence_context: object,
) -> dict[str, Any]:
    """Read the direct source-to-Spec verdict from the selected transaction.

    Prospective closeout always owns a builder-issued v11 evidence context
    before this scheduling decision. The planner asks that strict validator
    directly; it never reconstructs dashboard cards or treats a presentation
    cache as semantic evidence.
    """

    result: dict[str, Any] = {
        "required": False,
        "ready": False,
        "lane": V11_SOURCE_SPEC_SEMANTIC_LANE,
        "errors": [],
    }
    try:
        status_payload = json.loads(
            (folder / "status.json").read_text(encoding="utf-8")
        )
    except (OSError, json.JSONDecodeError) as exc:
        result["errors"] = [f"status.json is unreadable: {exc}"]
        return result
    if not _raw_source_spec_screening_requested(
        folder, status_payload, source_map
    ):
        return result
    result["required"] = True
    try:
        current, error = current_v11_direct_semantic_review_state(
            ROOT,
            folder,
            context=evidence_context,
        )
    except (OSError, RuntimeError, TypeError, ValueError) as exc:
        current, error = False, str(exc)
    result["ready"] = current
    result["errors"] = [] if current else [
        error or "current v11 direct semantic-review evidence is incomplete"
    ]
    result["validation_lane"] = "shared_evidence_run_context"
    return result
def _semantic_review_is_authoritatively_covered(plan: Mapping[str, Any]) -> bool:
    """Return whether a current v11 lane has replaced obsolete legacy rows."""

    lane = plan.get("semantic_review_authoritative_lane")
    return isinstance(lane, Mapping) and (
        lane.get("lane") == V11_SOURCE_SPEC_SEMANTIC_LANE
        and lane.get("required") is True
        and lane.get("ready") is True
        and lane.get("errors") == []
    )


def current_v11_live_lean_operational_plan(
    folder: Path,
    *,
    source_map: Mapping[str, Any],
    evidence_context: object,
) -> tuple[CurrentV11OperationalPlan | None, list[str]]:
    """Project a current v11 semantic lane onto Lean's live import closure.

    The dashboard cache is a presentation artifact. Once the exact evidence
    transaction has established the complete v11 source/Spec, paper
    prerequisite, and material-library judgments, rebuilding that cache cannot
    strengthen semantic acceptance. Operational closeout still needs a
    current paper-root Lean closure and compiled artifact set, so acquire those
    directly from Lean and freeze them for the strict worker.

    This path never creates or revises a semantic judgment. An incomplete v11
    lane returns ``None`` and leaves the legacy planner path fail-closed.
    """

    lane = current_v11_source_spec_semantic_lane(
        folder,
        source_map=source_map,
        evidence_context=evidence_context,
    )
    if lane.get("required") is not True or lane.get("ready") is not True:
        errors = lane.get("errors")
        return None, (
            [str(error) for error in errors]
            if isinstance(errors, list)
            else ["current v11 direct semantic-review evidence is incomplete"]
        )

    from scripts.current_closeout.primary_gate_transaction import (
        current_route_schema_preflight_findings,
    )

    configuration_findings = current_route_schema_preflight_findings(
        ROOT,
        folder,
        context=evidence_context,
    )
    configuration_errors = [
        finding.message
        for finding in configuration_findings
        if finding.severity == "ERROR"
    ]
    if configuration_errors:
        return None, configuration_errors

    plan: dict[str, Any] = {
        "schema": 2,
        "paper": folder.name,
        "acceptance_credential": False,
        "requires_fresh_strict_closeout": True,
        "cache_reusable": True,
        "semantic_review_authoritative_lane": lane,
        "summary": {
            "statement_reusable": 0,
            "statement_requires_review": 0,
            "statement_future_reuse_pin_missing": 0,
            "coverage_reusable": 0,
            "coverage_requires_review": 0,
            "coverage_future_reuse_pin_missing": 0,
            "retirement_candidates": 0,
        },
        "validator_identity_errors": {"statement": [], "coverage": []},
        "global_error": "",
        "planner_compatibility": {
            "semantic_input_lane": "current_v11_direct_ledgers",
            "semantic_material_identity": "strict_transaction_content_snapshot",
            "operational_input_lane": "lean_live_import_closure",
            "dashboard_manifest_required": False,
            "strict_closeout_remains_authoritative": True,
        },
    }

    try:
        provider = builder_issued_v11_lean_operational_provider(
            folder,
            evidence_context,
        )
    except (OSError, RuntimeError, TypeError, ValueError) as exc:
        return None, [
            "the current v11 Lean graph could not supply its operational "
            "closure snapshot: " + str(exc)
        ]
    if provider is None:
        return None, [
            "the current v11 semantic transaction retained no operational "
            "Lean closure provider"
        ]
    source_ledger, compiled_ledger, closure_errors, closure_receipt = (
        _root_import_closure_mutation_snapshots(ROOT, folder, provider)
    )
    if closure_errors or closure_receipt is None:
        # A missing compiled root is operational, not semantic. Preserve the
        # exact v11 authority and schedule one focused build before replanning;
        # never route through the dashboard manifest producer.
        plan.update(
            {
                "compiled_artifacts_ready": False,
                "compiled_validation_mode": "lean_live_import_closure",
                "compiled_invalidation_reasons": list(closure_errors),
                "intermediate_focused_build": (
                    "paper_build_required_without_semantic_rereview"
                ),
                "final_focused_build": "run_via_strict_closeout",
            }
        )
        return CurrentV11OperationalPlan.capture(plan), []
    try:
        lean_projection = build_lean_closure_operational_projection(
            ROOT, closure_receipt
        )
    except CloseoutPlanReceiptError as exc:
        return None, [str(exc)]
    if not provider.finalize_unchanged():
        return None, ["Lean import-closure inputs changed during v11 planning"]
    strict_snapshot, strict_error = _strict_transaction_content_snapshot(
        folder,
        evidence_context=evidence_context,
    )
    if strict_snapshot is None:
        return None, [strict_error]

    publication_inputs = CloseoutPlanPublicationInputs.capture(
        folder=folder,
        source_ledger=source_ledger,
        compiled_ledger=compiled_ledger,
        strict_transaction_snapshot=strict_snapshot,
        lean_closure_projection=lean_projection,
    )
    plan.update(
        {
            "compiled_artifacts_ready": True,
            "compiled_validation_mode": "lean_live_import_closure",
            "compiled_invalidation_reasons": [],
            "source_material_sha256": str(
                lean_projection.get("source_closure_sha256") or ""
            ),
            "compiled_material_sha256": str(
                lean_projection.get("compiled_closure_sha256") or ""
            ),
            "intermediate_focused_build": "reuse_current_lean_import_closure",
            "final_focused_build": "run_via_strict_closeout",
            "audit_material_sha256": publication_inputs.audit_material_sha256,
            "audit_material_identity": publication_inputs.audit_material_identity,
        }
    )
    return CurrentV11OperationalPlan.capture(
        plan,
        publication_inputs=publication_inputs,
    ), []




def _semantic_plan_requires_manual_repair(plan: Mapping[str, Any]) -> bool:
    """Return whether a reusable plan must stop before operational freezing."""

    if _semantic_review_is_authoritatively_covered(plan):
        return False
    summary = plan.get("summary")
    validator_identity_errors = plan.get("validator_identity_errors")
    summary = summary if isinstance(summary, Mapping) else {}
    validator_identity_errors = (
        validator_identity_errors
        if isinstance(validator_identity_errors, Mapping)
        else {}
    )
    validator_error_count = sum(
        len(value) if isinstance(value, list) else bool(value)
        for value in validator_identity_errors.values()
    )
    return (
        plan.get("cache_reusable") is True
        and bool(
            str(plan.get("global_error") or "")
            or validator_error_count
            or int(summary.get("statement_requires_review") or 0)
            or int(summary.get("coverage_requires_review") or 0)
        )
    )


def compact_plan_for_output(plan: Mapping[str, Any], paper: str) -> dict[str, Any]:
    """Show only current repair obligations on the normal operator surface.

    A complete v11 raw-source-to-expanded-Spec lane supersedes the legacy
    statement/coverage worklists for closeout.  Those historical ledgers stay
    available under ``--all-items`` and remain inputs to their own validators,
    but displaying their stale rows as current ``fresh_*_review`` actions made
    a ready paper look incomplete.  Keep one explicit diagnostic count here
    instead of silently deleting the fact that historical records exist.
    """

    compact = dict(plan)
    if _semantic_review_is_authoritatively_covered(plan):
        statement = plan.get("statement")
        coverage = plan.get("coverage")
        statement_count = len(statement) if isinstance(statement, Mapping) else 0
        coverage_count = len(coverage) if isinstance(coverage, Mapping) else 0
        retirement_candidates = 0
        if isinstance(statement, Mapping):
            retirement_candidates = sum(
                isinstance(value, Mapping)
                and value.get("retirement_candidate") is True
                for value in statement.values()
            )
        compact.pop("statement", None)
        compact.pop("coverage", None)
        compact["superseded_legacy_review_diagnostics"] = {
            "current_closeout_obligations": 0,
            "statement_records": statement_count,
            "coverage_records": coverage_count,
            "retirement_candidates": retirement_candidates,
            "reason": (
                "the current v11 raw-source-to-expanded-Spec lane is authoritative; "
                "legacy item records remain historical diagnostics"
            ),
        }
        compact["reusable_items_omitted_from_output"] = {
            "statement": statement_count,
            "coverage": coverage_count,
        }
        compact["full_item_plan_command"] = (
            f"python3 scripts/closeout_reuse_plan.py --paper {paper} --all-items"
        )
        return compact

    omitted: dict[str, int] = {}
    for lane in ("statement", "coverage"):
        raw_items = plan.get(lane)
        if not isinstance(raw_items, Mapping):
            continue
        compact[lane] = {
            key: value
            for key, value in raw_items.items()
            if not isinstance(value, Mapping) or value.get("reusable") is not True
        }
        omitted[lane] = len(raw_items) - len(compact[lane])
    compact["reusable_items_omitted_from_output"] = omitted
    compact["full_item_plan_command"] = (
        f"python3 scripts/closeout_reuse_plan.py --paper {paper} --all-items"
    )
    return compact


def operator_plan_for_output(
    plan: Mapping[str, Any], paper: str, *, all_items: bool
) -> dict[str, Any]:
    """Project the already presentation-only operator plan for output.

    Strict transaction and Lean-closure snapshots travel only through the
    separate immutable publication object, so this renderer has no hidden
    acceptance material to recognize or strip.
    """

    return dict(plan) if all_items else compact_plan_for_output(plan, paper)


def current_canonical_receipt_terminal_plan(
    folder: Path,
) -> dict[str, Any] | None:
    """Reuse current canonical acceptance and check its reader-facing documents.

    The canonical receipt is the acceptance boundary.  Its validator checks
    the exact source artifact and statement map, the transitive Lean interface
    closure, the selected review ledger, the focused-build receipt, the review
    protocol, and the graph's registered terminal engine authority. Reconstructing
    the semantic dashboard and the operational plan that produced an already
    current receipt cannot strengthen that result; it only recreates advisory
    scheduling state.  A missing or stale receipt therefore falls through to
    ordinary planning. A current receipt still needs a document preflight:
    missing or stale presentation artifacts schedule only document repair.

    This function never updates stage receipts or other paper evidence.  Those
    files are operational history, not prerequisites for continuing to trust a
    canonical receipt whose exact acceptance inputs remain current.
    """

    try:
        candidate = load_final_closure_receipt(ROOT, folder.name)
    except FinalClosureReceiptError:
        return None
    semantic_basis: str | None = None
    if candidate.payload.get("schema") == 6:
        try:
            semantic_basis = current_document_semantic_basis_sha256(
                folder,
                accepted_graph_only=True,
            )
        except (OSError, RuntimeError, TypeError, ValueError):
            # The accepted fast path never authorizes Lean recovery.  A stale
            # exact import closure falls through before the ordinary receipt
            # validator can attempt its separate recovery route.
            return None
    try:
        closure = validate_final_closure_receipt(ROOT, folder.name)
        if (
            closure.path.resolve() != candidate.path.resolve()
            or closure.payload != candidate.payload
        ):
            return None
        receipt_bytes = closure.path.read_bytes()
    except (FinalClosureReceiptError, OSError):
        return None
    payload = closure.payload
    plan = {
        "schema": 2,
        "paper": folder.name,
        "acceptance_credential": False,
        "requires_fresh_strict_closeout": False,
        "canonical_receipt_current": True,
        "closeout_complete": True,
        "readiness_matrix": {
            "ready": True,
            "state": "current_accepted_graph",
            "scope": (
                "all acceptance inputs bound and revalidated by the canonical "
                "final closure receipt"
            ),
        },
        "terminal_receipt_fast_path": {
            "used": True,
            "reason": (
                "the canonical receipt and every acceptance input it binds are "
                "current; semantic replanning would add no validation"
            ),
            "semantic_planner_reconstructed": False,
            "operational_stage_receipts_reissued": False,
        },
        "canonical_receipt": {
            "path": closure.path.relative_to(ROOT).as_posix(),
            "sha256": hashlib.sha256(receipt_bytes).hexdigest(),
            "evidence_lane": (
                "obligation-graph"
                if payload.get("schema") in {5, 6}
                else payload.get("evidence_lane")
            ),
            "closed_at": payload.get("closed_at"),
            "obligation_bundle": dict(payload.get("obligation_bundle") or {}),
            "accepted_graph": dict(payload.get("accepted_graph") or {}),
        },
        "next_action": None,
        "actions": [],
    }
    try:
        status_payload = json.loads((folder / "status.json").read_text(encoding="utf-8"))
    except (OSError, ValueError):
        status_payload = None
    preflight = _terminal_presentation_closeout_preflight(
        folder,
        status_payload,
        all_selected_semantic_review_sha256=semantic_basis,
    )
    if semantic_basis is not None:
        try:
            finalized_semantic_basis = current_document_semantic_basis_sha256(
                folder,
                accepted_graph_only=True,
            )
        except (OSError, RuntimeError, TypeError, ValueError):
            return None
        if finalized_semantic_basis != semantic_basis:
            return None
    if _stop_for_closeout_preflight(
        plan,
        key="terminal_presentation_preflight",
        preflight=preflight,
        action_id="complete_terminal_closeout_documents",
        fallback_reason="complete the reader-facing closeout documents",
    ):
        plan["closeout_complete"] = False
        plan["readiness_matrix"]["ready"] = False
        plan["readiness_matrix"]["state"] = "current_accepted_graph_documents_incomplete"
    return plan


def current_protocol_migration_plan(
    paper: str, static_readiness: Mapping[str, Any]
) -> dict[str, Any]:
    """Stop an unclosed legacy paper before any retired runtime is consulted."""

    action = {
        "id": "upgrade_to_current_protocol",
        "state": "ready_now",
        "required": True,
        "reason": (
            "this paper has no current accepted receipt and has not selected the "
            "graph-native v11 audit; prepare its typed source map, one semantic "
            "Spec per source claim, intake freeze, and v11 screening container "
            "before replanning"
        ),
        "migration_preserves_historical_status": True,
        "acceptance_credential": False,
    }
    return {
        "schema": 2,
        "paper": paper,
        "acceptance_credential": False,
        "requires_fresh_strict_closeout": True,
        "readiness_matrix": dict(static_readiness),
        "current_protocol": "migration_required",
        "historical_runtime_consulted": False,
        "expensive_planning_deferred": True,
        "next_action": action,
        "actions": [action],
    }


@dataclass(frozen=True)
class CurrentV11PrerequisiteStage:
    """One prerequisite decision plus the exact graph context it retained."""

    action: dict[str, Any] | None
    evidence_context: object | None


def current_v11_import_closure_action(folder: Path) -> dict[str, Any] | None:
    """Return the first graph prerequisite without opening graph authorities.

    Every fresh v11 graph and review queue is downstream of one portable,
    paper-root Lean import-closure carrier.  Checking that carrier must stay
    ahead of graph projection: otherwise an old or malformed screening can
    load the full graph/review engine merely to discover that its prerequisite
    is absent.  This helper reads only the saved carrier and invokes the exact
    current-content validator when the carrier has the expected entrypoint.
    It grants no semantic, graph, build, or closeout credit.
    """

    audit = folder / "audit"
    closure_receipt = audit / "LEAN_IMPORT_CLOSURE_RECEIPT.json"
    expected_closure_entrypoint = f"papers/{folder.name}.lean"
    try:
        closure_payload = json.loads(closure_receipt.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError):
        closure_payload = None
    closure_current_error = (
        _v11_lean_import_closure_current_error(folder, closure_payload)
        if isinstance(closure_payload, Mapping)
        and closure_payload.get("entrypoint") == expected_closure_entrypoint
        else ""
    )
    if (
        isinstance(closure_payload, Mapping)
        and closure_payload.get("entrypoint") == expected_closure_entrypoint
        and not closure_current_error
    ):
        return None
    return {
        "id": "record_current_lean_import_closure",
        "state": "ready_now",
        "reason": (
            "fresh v11 closeout needs Lean's transitive paper-build closure "
            "before semantic review; this portable carrier is not an "
            "acceptance credential"
            + (
                "; the saved carrier is not current: " + closure_current_error
                if closure_current_error
                else ""
            )
        ),
        "commands": [
            f"python3 scripts/final_closure_receipt.py --paper {folder.name} "
            "--record-current-lean-import-closure"
        ],
    }


def current_v11_prerequisite_stage(
    folder: Path,
    *,
    status_payload: Mapping[str, Any] | None = None,
    source_map_payload: Mapping[str, Any] | None = None,
) -> CurrentV11PrerequisiteStage:
    """Plan prerequisite review directly from one retained Lean graph.

    Accepted receipts return before this stage.  A new closeout first records
    the portable paper-root import closure, then loads the exact current graph
    checkpoint into one builder-issued evidence context.  The graph's targets,
    not a packet/dashboard cache, determine prerequisite deltas.  When every
    ledger is current, the same context is returned for the later strict gates.
    """

    status: object = status_payload
    if status is None:
        try:
            status = json.loads(
                (folder / "status.json").read_text(encoding="utf-8")
            )
        except (OSError, json.JSONDecodeError):
            return CurrentV11PrerequisiteStage(None, None)
    source_map: object = source_map_payload
    if source_map is None:
        try:
            source_map = json.loads(
                (folder / "audit" / "paper_statement_map.json").read_text(
                    encoding="utf-8"
                )
            )
        except (OSError, json.JSONDecodeError):
            source_map = None
    if not _raw_source_spec_screening_requested(folder, status, source_map):
        return CurrentV11PrerequisiteStage(None, None)
    audit = folder / "audit"
    closure_action = current_v11_import_closure_action(folder)
    if closure_action is not None:
        return CurrentV11PrerequisiteStage(closure_action, None)

    try:
        graph_projection = load_current_v11_review_graph_projection(ROOT, folder)
    except (OSError, RuntimeError, TypeError, ValueError) as exc:
        return CurrentV11PrerequisiteStage({
            "id": "repair_v11_lean_review_graph",
            "state": "inspection_required",
            "reason": (
                "the current non-accepting Lean review graph could not be "
                "validated: " + str(exc)
            ),
            "commands": [],
        }, None)
    if graph_projection is None:
        return CurrentV11PrerequisiteStage({
            "id": "prepare_v11_lean_review_graph",
            "state": "ready_now",
            "reason": (
                "fresh v11 closeout needs one complete Lean-owned graph before "
                "review; acquire its exact claim and prerequisite surfaces"
            ),
            "commands": [
                f"python3 scripts/closeout_reuse_plan.py --paper {folder.name} "
                "--prepare-v11-lean-review-graph"
            ],
        }, None)
    review_targets = graph_projection.target_material()

    paper_targets = review_targets.get("paper_prerequisite_targets")
    if (
        not (audit / "paper_semantic_prerequisites.json").is_file()
        and isinstance(paper_targets, Mapping)
        and not paper_targets
    ):
        return CurrentV11PrerequisiteStage({
            "id": "record_empty_paper_prerequisite_surface",
            "state": "ready_now",
            "reason": (
                "Lean proved that the paper-local prerequisite surface is empty; "
                "record the canonical zero-row ledger"
            ),
            "commands": [
                f"python3 scripts/reissue_paper_semantic_prerequisites.py --paper "
                f"{folder.name} --refresh-current --v11-review-graph --write"
            ],
        }, graph_projection.context)
    try:
        from scripts import reissue_library_semantic_review as library_reissue
        from scripts import (
            reissue_paper_semantic_prerequisites as paper_reissue,
        )

        paper_delta = paper_reissue.current_changed_decision_template_and_path(
            folder, review_graph=graph_projection
        )
        library_delta = library_reissue.current_changed_decision_template_and_path(
            folder, review_graph=graph_projection
        )
        paper_structural_refresh = bool(
            paper_delta is None
            and (audit / "paper_semantic_prerequisites.json").is_file()
            and paper_reissue.current_structural_refresh_required(
                folder,
                review_graph=graph_projection,
            )
        )
        library_structural_refresh = bool(
            library_delta is None
            and (audit / "library_semantic_review.json").is_file()
            and library_reissue.current_structural_refresh_required(
                folder,
                review_graph=graph_projection,
            )
        )
    except (OSError, RuntimeError, TypeError, ValueError) as exc:
        return CurrentV11PrerequisiteStage({
            "id": "repair_semantic_prerequisite_review_surface",
            "state": "inspection_required",
            "reason": (
                "the current graph could not be projected into the exact "
                "paper/library prerequisite-review delta: " + str(exc)
            ),
            "commands": [],
        }, graph_projection.context)

    # ``paper_prerequisite_targets`` is Lean's complete local dependency
    # closure. It can be nonempty even when the typed source map selects no
    # paper-local semantic prerequisite for review. In that case the reissue
    # projection correctly returns no delta, but closeout still needs the
    # canonical empty ledger; otherwise the final fall-through requests a
    # review with an empty command list.
    if (
        paper_delta is None
        and not (audit / "paper_semantic_prerequisites.json").is_file()
    ):
        return CurrentV11PrerequisiteStage({
            "id": "record_empty_paper_prerequisite_surface",
            "state": "ready_now",
            "reason": (
                "the typed source map selects no paper-local semantic "
                "prerequisite, although Lean retains local proof-support "
                "dependencies; record the canonical zero-row ledger"
            ),
            "commands": [
                f"python3 scripts/reissue_paper_semantic_prerequisites.py --paper "
                f"{folder.name} --refresh-current --v11-review-graph --write"
            ],
        }, graph_projection.context)

    if paper_delta is None and library_delta is None and (
        paper_structural_refresh or library_structural_refresh
    ):
        commands: list[str] = []
        if paper_structural_refresh:
            commands.append(
                f"python3 scripts/reissue_paper_semantic_prerequisites.py "
                f"--paper {folder.name} --refresh-current --v11-review-graph --write"
            )
        if library_structural_refresh:
            commands.append(
                f"python3 scripts/reissue_library_semantic_review.py "
                f"--paper {folder.name} --refresh-current --v11-review-graph --write"
            )
        return CurrentV11PrerequisiteStage({
            "id": "refresh_semantic_prerequisite_metadata",
            "state": "ready_now",
            "reason": (
                "all paper/library prerequisite judgments reuse exact semantic "
                "identities; rewrite only current declaration and source routing"
            ),
            "commands": commands,
        }, graph_projection.context)

    if (
        paper_delta is None
        and library_delta is None
        and (audit / "paper_semantic_prerequisites.json").is_file()
        and (audit / "library_semantic_review.json").is_file()
    ):
        return CurrentV11PrerequisiteStage(None, graph_projection.context)

    if (
        library_delta is None
        and not (audit / "library_semantic_review.json").is_file()
    ):
        return CurrentV11PrerequisiteStage({
            "id": "record_empty_library_prerequisite_surface",
            "state": "ready_now",
            "reason": (
                "Lean proved that the material library prerequisite surface is "
                "empty; record the canonical zero-row ledger"
            ),
            "commands": [
                f"python3 scripts/reissue_library_semantic_review.py --paper "
                f"{folder.name} --refresh-current --v11-review-graph --write"
            ],
        }, graph_projection.context)

    def queue_arg(path: Path) -> str:
        resolved = path.resolve()
        root = ROOT.resolve()
        return str(
            resolved.relative_to(root)
            if resolved.is_relative_to(root)
            else resolved
        )

    emit_commands: list[str] = []
    if paper_delta is not None and not paper_delta[1].is_file():
        paper_queue_arg = queue_arg(paper_delta[1])
        emit_commands.append(
            f"python3 scripts/reissue_paper_semantic_prerequisites.py --paper {folder.name} "
            f"--emit-template {paper_queue_arg} --v11-review-graph --changed-only"
        )
    if library_delta is not None and not library_delta[1].is_file():
        library_queue_arg = queue_arg(library_delta[1])
        emit_commands.append(
            f"python3 scripts/reissue_library_semantic_review.py --paper {folder.name} "
            f"--emit-template {library_queue_arg} --v11-review-graph --changed-only"
        )
    if emit_commands:
        return CurrentV11PrerequisiteStage({
            "id": "emit_semantic_prerequisite_review_queues",
            "state": "ready_now",
            "reason": (
                "the complete Lean prerequisite closure is current; emit "
                "content-addressed blank work queues only for new or changed "
                "semantic-prerequisite rows"
            ),
            "commands": emit_commands,
        }, graph_projection.context)

    issue_commands: list[str] = []
    if paper_delta is not None:
        paper_queue_arg = queue_arg(paper_delta[1])
        issue_commands.append(
            f"python3 scripts/reissue_paper_semantic_prerequisites.py --paper {folder.name} "
            f"--decisions {paper_queue_arg} --validator <reviewer-id> "
            "--v11-review-graph --write"
        )
    if library_delta is not None:
        library_queue_arg = queue_arg(library_delta[1])
        issue_commands.append(
            f"python3 scripts/reissue_library_semantic_review.py --paper {folder.name} "
            f"--decisions {library_queue_arg} --validator <reviewer-id> "
            "--v11-review-graph --write"
        )
    return CurrentV11PrerequisiteStage({
        "id": "review_semantic_prerequisites",
        "state": "review_required",
        "reason": (
            "inspect each changed raw-source/Lean pair, fill an explicit judgment "
            "and reason, then merge those decisions with every exact reusable row"
        ),
        "commands": issue_commands,
    }, graph_projection.context)


def current_approved_review_context_projection_action(
    folder: Path,
    source_map_payload: Mapping[str, Any],
) -> dict[str, Any] | None:
    """Schedule deterministic approval projection before reviewer bundles.

    Existing accepted receipts return before this prospective-closeout path.
    For a new or reopened closeout, the tracked preparation config and
    source-proof-fidelity ledger must already be reflected in the exact source
    map sent to independent reviewers.  The comparison is read-only; the
    returned command performs the explicit tracked update.
    """

    config_path = folder / "audit" / "v11_source_map_preparation_config.json"
    raw_items = source_map_payload.get("items")
    has_embedded_authority = isinstance(raw_items, Mapping) and any(
        isinstance(item, Mapping)
        and (
            "model_convention_ids" in item
            or "accepted_additional_assumptions" in item
        )
        for item in raw_items.values()
    )
    if (
        not config_path.is_file()
        and source_map_payload.get("approved_review_context_schema") != 1
        and not has_embedded_authority
    ):
        # Historical maps with no authority route remain readable under their
        # recorded closeout. A new current map opts in through either its
        # tracked config, its schema, or an explicit item-level authority.
        return None
    expected, error = expected_approved_review_context_projection(
        folder,
        source_map_payload,
    )
    if error or expected is None:
        return {
            "id": "repair_approved_review_context_projection",
            "state": "inspection_required",
            "reason": (
                "the tracked source-map preparation inputs could not be "
                "projected before semantic review: " + error
            ),
            "commands": [],
        }

    if current_approved_review_context_projection(source_map_payload) == expected:
        return None
    return {
        "id": "sync_approved_review_contexts",
        "state": "ready_now",
        "reason": (
            "project tracked maintainer-approved source readings and additions "
            "into the exact source map before generating semantic-review bundles"
        ),
        "commands": [
            (
                f"python3 scripts/sync_approved_review_contexts.py --paper "
                f"{folder.name} --write"
            )
        ],
    }


def current_v11_saved_screening_preflight_errors(folder: Path) -> list[str]:
    """Reject a malformed saved screening before any Lean graph acquisition.

    This is an ordering optimization only. A clean container grants no
    semantic credit: the ordinary v11 validator later checks every exact
    source row against the Lean-expanded target inside the frozen transaction.
    """

    path = folder / "audit" / "v11_raw_source_spec_screening.json"
    try:
        payload: object = json.loads(path.read_text(encoding="utf-8"))
    except (OSError, UnicodeDecodeError, json.JSONDecodeError):
        payload = None
    return list(
        validate_v11_screening_container(payload, paper=folder.name).errors
    )


def current_source_inventory_candidate_review_action(
    folder: Path,
    source_map: Mapping[str, Any],
) -> dict[str, Any] | None:
    """Schedule the bounded source-only upgrade before any Lean graph work.

    The final holistic surface needs an explicit candidate ledger, including an
    explicitly reviewed empty ledger.  Older completed inventories predate that
    field.  Route them through one content-addressed source-only queue rather
    than letting final closeout fail late or rerunning Lean semantic review.
    """

    try:
        from scripts import reissue_source_inventory_candidates as reissue

        current = reissue.current_decision_template_and_path(folder, source_map)
    except (OSError, RuntimeError, TypeError, ValueError) as exc:
        return {
            "id": "repair_source_inventory_candidate_surface",
            "state": "inspection_required",
            "required": True,
            "reason": "could not construct the source-only candidate queue: " + str(exc),
            "commands": [],
        }
    if current is None:
        return None
    template, queue_path = current
    try:
        queue_relative = queue_path.resolve().relative_to(ROOT.resolve()).as_posix()
    except ValueError:
        return {
            "id": "repair_source_inventory_candidate_surface",
            "state": "inspection_required",
            "required": True,
            "reason": "the candidate review queue path is outside the repository",
            "commands": [],
        }
    if not queue_path.is_file():
        return {
            "id": "emit_source_inventory_candidate_review_queue",
            "state": "ready_now",
            "required": True,
            "reason": (
                "the completed source inventory predates the explicit candidate "
                "surface; emit one source-bound non-evidence queue before any Lean "
                "graph acquisition or semantic replay"
            ),
            "commands": [
                "python3 scripts/reissue_source_inventory_candidates.py "
                f"--paper {folder.name} --emit-current-template"
            ],
        }
    queue_error = reissue.current_decision_queue_error(
        folder,
        queue_path,
        template=template,
    )
    if queue_error:
        return {
            "id": "repair_source_inventory_candidate_review_queue",
            "state": "inspection_required",
            "required": True,
            "reason": (
                f"the candidate review queue `{queue_relative}` is stale or "
                "malformed: " + queue_error
            ),
            "commands": [],
        }
    ready = reissue.decision_queue_ready(
        folder,
        queue_path,
        template=template,
    )
    return {
        "id": "apply_source_inventory_candidate_review"
        if ready
        else "review_source_inventory_candidates",
        "state": "review_required",
        "required": True,
        "reason": (
            "apply the completed source-only candidate and holistic review"
            if ready
            else (
                "classify each mechanically discovered candidate and read the "
                "complete pinned source for any additional material mathematical "
                "presentation; this does not reopen Lean semantic judgments"
            )
        ),
        "commands": [
            "python3 scripts/reissue_source_inventory_candidates.py "
            f"--paper {folder.name} --decisions {queue_relative} "
            "--validator <reviewer-id> --write"
        ],
    }


def current_v11_screening_repair_action(
    folder: Path,
    screening_errors: Iterable[object],
) -> dict[str, Any]:
    """Return the exact no-extra-Lean source/Spec review action.

    The unified graph projection is already current when this helper runs. A
    content-addressed non-evidence queue preserves any earlier
    human annotations under their old identity while giving this exact source
    and Lean surface one deterministic review path. The receipt writer still
    requires an explicit reviewer verdict and revalidates every current byte.
    """

    errors = [str(item).strip() for item in screening_errors if str(item).strip()]
    try:
        from scripts import reissue_v11_raw_source_spec_screening as reissue

        review_graph = load_current_v11_review_graph_projection(ROOT, folder)
        if review_graph is None:
            raise ValueError("the exact-current v11 review graph is unavailable")
        delta = reissue.current_changed_decision_template_and_path(
            folder,
            review_graph=review_graph,
        )
    except (OSError, RuntimeError, TypeError, ValueError) as exc:
        return {
            "id": "run_draft_semantic_preflight",
            "state": "review_required",
            "required": True,
            "reason": (
                "the saved screening cannot be repaired from a current graph: "
                + str(exc)
                + ". Before acquiring the one review graph, give a context-isolated "
                "reviewer the stdout-only raw-source/expanded-Spec preflight and "
                "repair any source/interface mismatch it finds. This is diagnostic "
                "only and grants no semantic or closeout credit. After a clean "
                "preflight (or the required repairs), prepare the graph once using "
                "the ordinary graph command rather than rerunning this planner action."
            ),
            "commands": [
                f"python3 scripts/draft_semantic_preflight.py --paper {folder.name}"
            ],
        }
    if delta is None:
        return {
            "id": "repair_current_v11_screening_metadata",
            "state": "ready_now",
            "required": True,
            "reason": (
                "; ".join(errors)
                + ("; " if errors else "")
                + "the source/Spec semantic identities are reusable, so the "
                "remaining screening defect is derived routing or renderer "
                "provenance rather than new reviewer work"
            ),
            "commands": [
                f"python3 scripts/reissue_v11_raw_source_spec_screening.py "
                f"--paper {folder.name} --refresh-current --v11-review-graph --write"
            ],
        }
    template, queue_path = delta
    try:
        queue_relative = queue_path.resolve().relative_to(ROOT.resolve()).as_posix()
    except ValueError:
        return {
            "id": "repair_current_v11_review_queue",
            "state": "inspection_required",
            "required": True,
            "reason": "the current v11 review queue path is outside the repository",
            "commands": [],
        }
    if not queue_path.is_file():
        return {
            "id": "emit_current_v11_source_spec_review_queue",
            "state": "ready_now",
            "required": True,
            "reason": (
                "; ".join(errors)
                + ("; " if errors else "")
                + "emit one content-addressed non-evidence queue containing only "
                "changed source/Spec semantic identities from the current unified "
                "Lean graph; this issues no semantic judgment"
            ),
            "commands": [
                f"python3 scripts/reissue_v11_raw_source_spec_screening.py "
                f"--paper {folder.name} --emit-current-template --v11-review-graph"
            ],
        }
    queue_error = reissue.current_decision_queue_error(
        queue_path,
        template=template,
        paper=folder.name,
    )
    if queue_error:
        return {
            "id": "repair_current_v11_review_queue",
            "state": "inspection_required",
            "required": True,
            "reason": (
                f"the content-addressed non-evidence queue `{queue_relative}` is "
                "corrupt or was edited outside its review schema: " + queue_error
            ),
            "commands": [],
        }
    return {
        "id": "review_current_v11_source_spec_matches",
        "state": "review_required",
        "required": True,
        "reason": (
            "; ".join(errors)
            + ("; " if errors else "")
            + "inspect each changed exact source/Lean pair, fill one explicit verdict "
            "and reason, then merge it with every reusable current screening row"
        ),
        "commands": [
            f"python3 scripts/reissue_v11_raw_source_spec_screening.py "
            f"--paper {folder.name} --decisions {queue_relative} "
            "--validator <reviewer-id> --v11-review-graph --write"
        ],
    }


def _closeout_plan_input_paths(
    folder: Path,
    *,
    strict_transaction_content_snapshot: Mapping[str, object],
) -> tuple[list[Path], list[Path]]:
    """Compatibility export for the package receipt-writer selection rule."""

    return closeout_plan_input_paths(
        ROOT,
        folder,
        strict_transaction_content_snapshot=strict_transaction_content_snapshot,
    )


def _closeout_plan_publication_input_identity(
    *,
    folder: Path,
    publication_inputs: CloseoutPlanPublicationInputs | None,
) -> str:
    return publication_input_identity(
        folder=folder,
        publication_inputs=publication_inputs,
    )


def _write_current_closeout_plan_receipt(
    plan: Mapping[str, Any],
    *,
    folder: Path,
    deep_paper_prose: bool,
    publication_inputs: CloseoutPlanPublicationInputs | None,
) -> CloseoutPlanReceiptPublication:
    """Delegate receipt writing to the closed package service."""

    return publish_closeout_plan_receipt(
        ROOT,
        plan,
        folder=folder,
        deep_paper_prose=deep_paper_prose,
        publication_inputs=publication_inputs,
    )


def _current_closeout_stage_projection(
    *, canonical_receipt_current: bool = False
) -> dict[str, object]:
    """Describe only the actual current executor gates.

    Planner-ready semantic artifacts are inputs, not completed execution
    stages. Historical content-addressed stage receipts remain readable through
    ``closeout_pipeline`` but no longer participate in current planning or
    publication.
    """

    completed = STRICT_CLOSEOUT_EXECUTION_STAGES if canonical_receipt_current else ()
    return current_closeout_execution_projection(completed)


def persist_v11_operational_lean_graph(
    folder: Path,
    evidence_context: object | None,
) -> str:
    """Compatibility export of the graph owner's checkpoint operation."""

    return persist_retained_v11_lean_review_graph(
        ROOT,
        folder,
        evidence_context,
    )


def _v11_worker_disposition(
    prior_execution: Mapping[str, Any] | None,
    *,
    prior_execution_error: str,
    plan_identity: str,
) -> V11WorkerDisposition:
    """Classify a worker only by its relation to this exact v11 plan."""

    return classify_v11_worker_disposition(
        prior_execution,
        prior_execution_error=prior_execution_error,
        plan_identity=plan_identity,
        plan_identity_schema=OPERATIONAL_PLAN_IDENTITY_SCHEMA,
    )


def _v11_action_schedule(
    *,
    paper: str,
    plan_identity: str,
    final_holistic_surface_identity: str,
    prior_execution: Mapping[str, Any] | None,
    prior_execution_error: str,
    deep_paper_prose: bool,
    final_holistic_audit_ready: bool,
    final_holistic_audit_errors: Iterable[str],
    realization_receipt_preflight: Mapping[str, Any],
    summary: Mapping[str, Any],
) -> dict[str, Any]:
    """Project a late validated state through the one v11 action adapter."""

    final_errors = tuple(str(error) for error in final_holistic_audit_errors)
    worker = _v11_worker_disposition(
        prior_execution,
        prior_execution_error=prior_execution_error,
        plan_identity=plan_identity,
    )
    state = V11CloseoutState(
        structure_current=True,
        lean_graph_current=True,
        semantic_review_current=True,
        compiled_inputs_current=True,
        realization_current=(
            realization_receipt_preflight.get("current") is True
        ),
        plan_identity_current=bool(plan_identity),
        final_source_audit_current=final_holistic_audit_ready,
        accepted_graph_current=False,
        worker=worker,
    )
    return schedule_v11_closeout(
        state,
        paper=paper,
        plan_identity=plan_identity,
        final_holistic_surface_identity=final_holistic_surface_identity,
        deep_paper_prose=deep_paper_prose,
        realization_receipt_preflight=realization_receipt_preflight,
        final_source_audit_errors=final_errors,
        prior_execution_error=prior_execution_error,
        summary=summary,
        include_final_source_audit_projection=True,
    )


def _v11_preplan_action_schedule(
    paper: str,
    *,
    semantic_review_current: bool,
    compiled_inputs_current: bool,
    realization_receipt_preflight: Mapping[str, Any] | None = None,
    summary: Mapping[str, Any] | None = None,
    semantic_errors: Iterable[str] = (),
) -> dict[str, Any]:
    """Project an early validated state through the same v11 action adapter."""

    preflight = dict(
        realization_receipt_preflight
        or {"state": "not_checked", "current": True, "required": False}
    )
    state = V11CloseoutState(
        structure_current=True,
        lean_graph_current=True,
        semantic_review_current=semantic_review_current,
        compiled_inputs_current=compiled_inputs_current,
        realization_current=preflight.get("current") is True,
        plan_identity_current=True,
        final_source_audit_current=True,
        accepted_graph_current=False,
    )
    return schedule_v11_closeout(
        state,
        paper=paper,
        semantic_errors=semantic_errors,
        realization_receipt_preflight=preflight,
        summary=summary,
    )


def finalize_operational_plan(
    plan: dict[str, Any],
    *,
    folder: Path,
    source_coverage_mode: str,
    execution_path: Path,
    static_readiness: Mapping[str, Any],
    publication_inputs: CloseoutPlanPublicationInputs | None = None,
    evidence_context: object | None = None,
    v11_lean_graph_persistence_error: str = "",
) -> dict[str, Any]:
    """Attach scheduling after this planner snapshot's terminal receipt miss.

    ``main`` runs the complete canonical-receipt validator before prospective
    planning. Reaching this function therefore records a receipt miss for the
    immutable invocation; no read-only planning step can turn it into current
    acceptance. A receipt published concurrently is observed by the next
    planner invocation.
    """

    plan["readiness_matrix"] = dict(static_readiness)
    deep_paper_prose = source_coverage_mode == DEEP_PAPER_WITH_ALL_PROSE_CLAIMS
    plan["source_coverage_mode"] = source_coverage_mode
    if v11_lean_graph_persistence_error:
        plan["v11_lean_review_graph_checkpoint_error"] = (
            v11_lean_graph_persistence_error
        )
    if _semantic_plan_requires_manual_repair(plan):
        # A semantic worklist cannot launch a worker, so it has no use for a
        # strict-input receipt, compiled ledger, or prior execution identity.
        # Returning before those operations prevents an invalid sidecar from
        # repeatedly paying for strict-context construction.
        plan.update(
            _v11_preplan_action_schedule(
                folder.name,
                semantic_review_current=False,
                compiled_inputs_current=(
                    plan.get("compiled_artifacts_ready") is True
                ),
                summary=(
                    plan.get("summary")
                    if isinstance(plan.get("summary"), Mapping)
                    else {}
                ),
                semantic_errors=(str(plan.get("global_error") or ""),),
            )
        )
        return plan

    if (
        plan.get("cache_reusable") is True
        and plan.get("compiled_artifacts_ready") is not True
    ):
        # A focused build necessarily changes the compiled closure.  Schedule
        # it before freezing strict inputs or a worker receipt, then replan
        # against the rebuilt artifact without reopening semantic review.
        plan.update(
            _v11_preplan_action_schedule(
                folder.name,
                semantic_review_current=True,
                compiled_inputs_current=False,
                summary=(
                    plan.get("summary")
                    if isinstance(plan.get("summary"), Mapping)
                    else {}
                ),
            )
        )
        return plan
    realization_receipt_preflight = current_graph_realization_preflight(
        folder,
        evidence_context=evidence_context,
    )
    plan["realization_receipt_preflight"] = realization_receipt_preflight
    if realization_receipt_preflight.get("current") is not True:
        # A selected current graph must authenticate every source-to-Spec proof
        # realization directly.  Surface a graph/route repair before any strict
        # worker can spend time; never rewrite a historical correspondence
        # worksheet as a current transition.
        plan.update(
            _v11_preplan_action_schedule(
                folder.name,
                semantic_review_current=True,
                compiled_inputs_current=True,
                summary=(
                    plan.get("summary")
                    if isinstance(plan.get("summary"), Mapping)
                    else {}
                ),
                realization_receipt_preflight=realization_receipt_preflight,
            )
        )
        return plan

    if evidence_context is not None:
        status_payload = getattr(evidence_context, "status_payload", None)
        terminal_preflight = _terminal_presentation_closeout_preflight(
            folder,
            status_payload,
        )
        if _stop_for_closeout_preflight(
            plan,
            key="terminal_presentation_closeout_preflight",
            preflight=terminal_preflight,
            action_id="complete_terminal_closeout_documents",
            fallback_reason=(
                "the final report and dependency DAG are not terminal-ready"
            ),
            after_semantic_review=True,
        ):
            return plan
    (
        prior_execution,
        prior_execution_error,
        prior_execution_namespace,
        _effective_execution_path,
    ) = effective_closeout_execution_state(ROOT, folder.name)
    if not prior_execution_error and prior_execution is not None:
        plan["last_closeout_execution"] = {
            "namespace": prior_execution_namespace,
            "state": prior_execution.get("state"),
            "launch_id": prior_execution.get("launch_id"),
            "started_at": prior_execution.get("started_at"),
            "completed_at": prior_execution.get("completed_at"),
            "exit_code": prior_execution.get("exit_code"),
            "result": prior_execution.get("result"),
            "acceptance_credential": False,
        }
    elif prior_execution_error:
        plan["last_closeout_execution_error"] = prior_execution_error
    plan["plan_identity_schema"] = OPERATIONAL_PLAN_IDENTITY_SCHEMA
    current_v11_graph_required = False
    if evidence_context is not None and _semantic_review_is_authoritatively_covered(
        plan
    ):
        current_v11_graph_required = (
            getattr(evidence_context, "source_semantic_lane", "")
            == V11_LEAN_CLAIM_GRAPH_EVIDENCE_LANE
        )
    if current_v11_graph_required:
        try:
            graph_carrier = builder_issued_v11_lean_review_graph_carrier(
                folder,
                evidence_context,
                repository_root=ROOT,
            )
        except (OSError, RuntimeError, TypeError, ValueError) as exc:
            graph_carrier = None
            plan["v11_lean_review_graph_error"] = str(exc)
        if graph_carrier is not None:
            try:
                from scripts.current_closeout.semantic_review import (
                    all_selected_semantic_review_material_sha256,
                    current_v11_semantic_review_result,
                )

                semantic_review_result = current_v11_semantic_review_result(
                    ROOT,
                    folder,
                    context=evidence_context,
                )
                all_selected_semantic_review_sha256 = (
                    all_selected_semantic_review_material_sha256(
                        semantic_review_result
                    )
                )
                final_holistic_audit_surface = (
                    build_final_holistic_audit_surface_from_repository(
                        ROOT,
                        paper=folder.name,
                        graph=graph_carrier,
                        status_projection=paper_status_acceptance_projection(
                            ROOT, folder.name
                        ),
                    )
                )
                if publication_inputs is not None:
                    publication_inputs = publication_inputs.with_review_surfaces(
                        v11_lean_review_graph=graph_carrier,
                        final_holistic_audit_surface=final_holistic_audit_surface,
                        all_selected_semantic_review_sha256=(
                            all_selected_semantic_review_sha256
                        ),
                    )
            except (
                FinalHolisticAuditSurfaceError,
                CloseoutStatusProjectionError,
                OSError,
                RuntimeError,
                TypeError,
                ValueError,
            ) as exc:
                plan["v11_lean_review_graph_error"] = (
                    "could not construct the typed final holistic audit surface: "
                    + str(exc)
                )
                graph_carrier = None
        if graph_carrier is None:
            reason = str(
                plan.get("v11_lean_review_graph_error")
                or "the current v11 semantic transaction retained no Lean graph"
            )
            stop_action = {
                "id": "resolve_current_v11_lean_review_graph",
                "state": "ready_now",
                "required": True,
                "reason": (
                    "the planner cannot publish a current v11 closeout without "
                    "transporting its already validated Lean graph to the strict "
                    "worker: "
                    + reason
                ),
            }
            plan.update(
                {
                    "plan_identity_sha256": "",
                    "plan_identity_input_path_count": 0,
                    "next_action": stop_action,
                    "actions": [stop_action],
                }
            )
            return plan
    publication = _write_current_closeout_plan_receipt(
        plan,
        folder=folder,
        deep_paper_prose=deep_paper_prose,
        publication_inputs=publication_inputs,
    )
    if publication.receipt is None:
        replan_argv = [
            "python3",
            "scripts/closeout_reuse_plan.py",
            "--paper",
            folder.name,
        ]
        replan_action = {
            "id": "replan_current_inputs",
            "state": "ready_now",
            "required": True,
            "argv": replan_argv,
            "command": shlex.join(replan_argv),
            "retryable": publication.disposition
            in {"source_race", "compiled_race"},
            "publication_disposition": publication.disposition,
            "input_identity_sha256": publication.input_identity_sha256,
            "reason": (
                "the exact operational input snapshot could not be frozen; "
                "discard this plan and reacquire current inputs: " + publication.error
            ),
        }
        plan.update(
            {
                "plan_identity_sha256": "",
                "plan_identity_input_path_count": 0,
                "operational_plan_error": publication.error,
                "operational_plan_publication_disposition": publication.disposition,
                "next_action": replan_action,
                "actions": [replan_action],
            }
        )
        return plan
    receipt = publication.receipt
    plan["plan_identity_sha256"] = str(receipt["plan_identity_sha256"])
    plan["plan_identity_input_path_count"] = len(
        receipt.get("content_inputs", {})
    ) + len(receipt.get("compiled_inputs", {}))
    plan["plan_receipt_path"] = str(
        closeout_plan_receipt_path(
            ROOT,
            folder.name,
            plan["plan_identity_sha256"],
        ).relative_to(ROOT)
    )
    plan["plan_receipt_acceptance_credential"] = False
    final_holistic_surface_identity = str(
        receipt.get("final_holistic_audit_surface_sha256") or ""
    ).strip().lower()
    if current_v11_graph_required and not SHA256_RE.fullmatch(
        final_holistic_surface_identity
    ):
        raise ValueError(
            "current v11 plan has no typed final holistic audit surface identity"
        )
    plan["final_holistic_audit_surface_sha256"] = (
        final_holistic_surface_identity
    )
    all_selected_semantic_review_identity = str(
        receipt.get("all_selected_semantic_review_sha256") or ""
    ).strip().lower()
    if current_v11_graph_required and not SHA256_RE.fullmatch(
        all_selected_semantic_review_identity
    ):
        raise ValueError(
            "current v11 plan has no all-selected semantic-review identity"
        )
    plan["all_selected_semantic_review_sha256"] = (
        all_selected_semantic_review_identity
    )
    frozen_final_holistic_surface = resolved_plan_final_holistic_audit_surface(
        ROOT, receipt
    )
    frozen_review_policy_assurance = (
        frozen_final_holistic_surface.get("review_policy_assurance")
        if isinstance(frozen_final_holistic_surface, Mapping)
        and isinstance(
            frozen_final_holistic_surface.get("review_policy_assurance"), Mapping
        )
        else None
    )
    final_holistic_errors = (
        final_holistic_audit_hard_errors(
            folder,
            target_surface_identity=final_holistic_surface_identity,
            review_policy_assurance=frozen_review_policy_assurance,
        )
        if current_v11_graph_required
        else []
    )
    final_holistic_ready = not final_holistic_errors
    plan["final_holistic_audit"] = {
        "required": current_v11_graph_required,
        "ready": final_holistic_ready,
        "state": (
            "current"
            if current_v11_graph_required and final_holistic_ready
            else "review_required"
            if current_v11_graph_required
            else "not_required"
        ),
        "target_surface_identity": (
            final_holistic_surface_identity if current_v11_graph_required else ""
        ),
        "errors": [
            {
                "path": error.path.relative_to(ROOT).as_posix(),
                "message": error.message,
            }
            for error in final_holistic_errors
        ],
        "acceptance_credential": False,
    }
    summary = plan.get("summary") if isinstance(plan.get("summary"), Mapping) else {}
    if not current_v11_graph_required:
        raise ValueError(
            "prospective closeout reached finalization without the current v11 graph"
        )
    # The current protocol cannot represent legacy adoption, dashboard cache
    # state, or an unbound worker completion. Its validated facts go through
    # the closed v11 reducer and exactly one operational adapter.
    schedule = _v11_action_schedule(
        paper=folder.name,
        plan_identity=plan["plan_identity_sha256"],
        final_holistic_surface_identity=final_holistic_surface_identity,
        prior_execution=(
            prior_execution if isinstance(prior_execution, Mapping) else None
        ),
        prior_execution_error=prior_execution_error,
        deep_paper_prose=deep_paper_prose,
        final_holistic_audit_ready=final_holistic_ready,
        final_holistic_audit_errors=(
            error.message for error in final_holistic_errors
        ),
        realization_receipt_preflight=realization_receipt_preflight,
        summary=summary,
    )
    plan.update(schedule)
    plan["closeout_stage_dag"] = _current_closeout_stage_projection(
        canonical_receipt_current=(schedule.get("closeout_complete") is True)
    )
    return plan


def execute_prepare_v11_lean_review_graph(folder: Path) -> int:
    """Run the planner-issued, non-accepting unified graph producer."""

    engine_error = runtime_engine_registration_error(ROOT)
    if engine_error:
        print(
            json.dumps(
                {
                    "schema": 1,
                    "paper": folder.name,
                    "acceptance_credential": False,
                    "prepared": False,
                    "error": engine_error,
                },
                indent=2,
                sort_keys=True,
            )
        )
        return 2
    preflight = v11_structural_graph_input_preflight(
        folder,
        require_prerequisite_ledger_bindings=False,
    )
    if preflight is None or preflight.get("current") is not True:
        print(
            json.dumps(
                {
                    "schema": 1,
                    "paper": folder.name,
                    "acceptance_credential": False,
                    "prepared": False,
                    "structural_preflight": preflight,
                    "error": (
                        "the typed source/Spec graph is not ready for Lean "
                        "review-graph preparation"
                    ),
                },
                indent=2,
                sort_keys=True,
            )
        )
        return 2
    try:
        prepared = dict(prepare_v11_lean_review_graph(ROOT, folder))
    except (OSError, RuntimeError, TypeError, ValueError) as exc:
        print(
            json.dumps(
                {
                    "schema": 1,
                    "paper": folder.name,
                    "acceptance_credential": False,
                    "prepared": False,
                    "error": str(exc),
                },
                indent=2,
                sort_keys=True,
            )
        )
        return 2
    prepared["prepared"] = True
    print(json.dumps(prepared, indent=2, sort_keys=True))
    return 0


def current_document_semantic_basis_sha256(
    folder: Path,
    *,
    accepted_graph_only: bool = False,
) -> str:
    """Return one current all-selected digest without acquiring a Lean graph."""

    from scripts.current_closeout.evidence_transaction import (
        build_current_v11_context_with_graph_checkpoint,
    )
    from scripts.current_closeout.semantic_review import (
        accepted_graph_all_selected_semantic_review_material_sha256,
        all_selected_semantic_review_material_sha256,
        current_v11_semantic_review_result,
    )

    context = build_current_v11_context_with_graph_checkpoint(
        folder,
        repository_root=ROOT,
    )
    if accepted_graph_only or context.v11_lean_review_graph_payload is None:
        return accepted_graph_all_selected_semantic_review_material_sha256(
            ROOT,
            folder,
            context=context,
        )
    result = current_v11_semantic_review_result(
        ROOT,
        folder,
        context=context,
        require_graph_checkpoint=True,
    )
    return all_selected_semantic_review_material_sha256(result)


def execute_document_semantic_basis(folder: Path) -> int:
    """Print a read-only document basis from current authenticated semantics.

    The migration helper revalidates existing source, target, judgment, and
    prerequisite identities.  It never schedules reviewer work, prepares a
    graph, writes a receipt, or grants closeout authority.
    """

    try:
        digest = current_document_semantic_basis_sha256(folder)
    except (OSError, RuntimeError, TypeError, ValueError) as exc:
        print(
            json.dumps(
                {
                    "schema": 1,
                    "paper": folder.name,
                    "acceptance_credential": False,
                    "document_basis_only": True,
                    "current": False,
                    "error": str(exc),
                },
                indent=2,
                sort_keys=True,
            )
        )
        return 2
    print(
        json.dumps(
            {
                "schema": 1,
                "paper": folder.name,
                "acceptance_credential": False,
                "document_basis_only": True,
                "current": True,
                "all_selected_semantic_review_sha256": digest,
            },
            indent=2,
            sort_keys=True,
        )
    )
    return 0


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--paper", required=True, help="Paper folder name under papers/."
    )
    parser.add_argument(
        "--all-items",
        action="store_true",
        help="include successful reusable items as well as repair obligations",
    )
    parser.add_argument(
        "--verify-compiled-content",
        action="store_true",
        help=(
            "force the diagnostic exact-content manifest path; ordinary planning "
            "already retains exact hashes and refreshes only changed stat guards"
        ),
    )
    parser.add_argument(
        "--diagnose",
        action="store_true",
        help=(
            "read only static/status paper readiness; never writes a plan, runs "
            "semantic reuse, or grants acceptance"
        ),
    )
    parser.add_argument(
        "--prepare-v11-lean-review-graph",
        action="store_true",
        help=(
            "acquire the one non-accepting Lean graph and packet projection "
            "needed before current-protocol semantic review"
        ),
    )
    parser.add_argument(
        "--document-semantic-basis",
        action="store_true",
        help=(
            "read the existing graph checkpoint and print the all-selected "
            "semantic identity needed to migrate reader documents"
        ),
    )
    args = parser.parse_args()

    folder = resolve_paper_folder(ROOT, args.paper)
    if folder is None:
        raise SystemExit(f"unknown paper folder: {args.paper}")
    if args.prepare_v11_lean_review_graph:
        if (
            args.diagnose
            or args.all_items
            or args.verify_compiled_content
            or args.document_semantic_basis
        ):
            raise SystemExit(
                "--prepare-v11-lean-review-graph cannot be combined with other modes"
            )
        return execute_prepare_v11_lean_review_graph(folder)
    if args.document_semantic_basis:
        if args.diagnose or args.all_items or args.verify_compiled_content:
            raise SystemExit(
                "--document-semantic-basis cannot be combined with other modes"
            )
        return execute_document_semantic_basis(folder)
    if args.diagnose:
        # Diagnose is a read-only aggregation surface. It reports operational
        # execution disposition alongside every deterministic local blocker;
        # normal planning below keeps the exclusive worker/recovery returns.
        execution_path = closeout_worker_state_path(args.paper)
        active_execution = running_execution_summary(execution_path)
        legacy_execution_path = default_closeout_execution_path(ROOT, args.paper)
        legacy_active_execution = running_execution_summary(legacy_execution_path)
        if active_execution is None:
            active_execution = legacy_active_execution
        (
            _prior_execution,
            early_execution_error,
            early_execution_namespace,
            early_execution_path,
        ) = effective_closeout_execution_state(ROOT, args.paper)
        engine_error = runtime_engine_registration_error(ROOT)
        # Diagnose reports cheap paper-local metadata only.  The exact intake
        # atom scan is deliberately reserved for an eligible normal closeout.
        static_readiness = static_closeout_readiness(
            folder,
            include_intake=False,
            require_terminal_documents=False,
        )
        paper_status, status_error = _paper_closeout_status_preflight(folder)
        diagnostic_actions: list[dict[str, Any]] = []
        if active_execution is not None:
            diagnostic_actions.append(
                {
                    "id": "inspect_active_closeout",
                    "state": "ready_now",
                    "required": True,
                    "reason": (
                        "an existing closeout execution is active; inspect its status "
                        "before starting another closeout"
                    ),
                }
            )
        if early_execution_error:
            status_argv = [
                "python3",
                "scripts/run_paper_closeout.py",
                "--paper",
                args.paper,
                "--status",
            ]
            diagnostic_actions.append(
                {
                    "id": "inspect_closeout_recovery",
                    "state": "ready_now",
                    "required": True,
                    "argv": status_argv,
                    "command": shlex.join(status_argv),
                    "reason": early_execution_error,
                }
            )
        if engine_error:
            diagnostic_actions.append(
                {
                    "id": "commit_registered_engine_transition",
                    "state": "ready_now",
                    "required": True,
                    "reason": engine_error,
                }
            )
        if not static_readiness["ready"]:
            diagnostic_actions.append(
                {
                    "id": "resolve_static_closeout_blockers",
                    "state": "ready_now",
                    "required": True,
                    "reason": "finish the listed deterministic paper-local obligations",
                }
            )
        if status_error:
            diagnostic_actions.append(
                {
                    "id": "resolve_paper_closeout_eligibility",
                    "state": "ready_now",
                    "required": True,
                    "reason": status_error,
                }
            )
        if not diagnostic_actions:
            diagnostic_actions.append(
                {
                    "id": "run_frozen_closeout_planner",
                    "state": "ready_now",
                    "required": True,
                    "reason": (
                        "static/status readiness passed; rerun without --diagnose to "
                        "perform the bounded raw-identity preflight and plan work"
                    ),
                }
            )
        payload: dict[str, Any] = {
            "schema": 2,
            "paper": args.paper,
            "acceptance_credential": False,
            "diagnostic_only": True,
            "strict_closeout_required_for_acceptance": True,
            "expensive_planning_deferred": True,
            "readiness_matrix": static_readiness,
            "next_action": diagnostic_actions[0],
            "actions": diagnostic_actions,
        }
        if active_execution is not None:
            payload.update(
                {
                    "start_another_closeout": False,
                    "closeout_start_disposition": "already_running",
                    "active_execution": active_execution,
                }
            )
        if early_execution_error:
            payload.update(
                {
                    "execution_namespace": early_execution_namespace,
                    "execution_path": str(early_execution_path.relative_to(ROOT)),
                }
            )
        if engine_error:
            payload["engine_registration_error"] = engine_error
            payload["after_engine_registration"] = (
                "rerun closeout_reuse_plan without --diagnose; no semantic cache, "
                "raw receipt, or execution identity was used"
            )
        if paper_status:
            payload["paper_status"] = paper_status
        print(json.dumps(payload, indent=2, sort_keys=True))
        return 0

    execution_path = closeout_worker_state_path(args.paper)
    active_execution = running_execution_summary(execution_path)
    legacy_execution_path = default_closeout_execution_path(ROOT, args.paper)
    legacy_active_execution = running_execution_summary(legacy_execution_path)
    if active_execution is None:
        active_execution = legacy_active_execution
    if active_execution is not None:
        print(
            json.dumps(
                {
                    "schema": 2,
                    "paper": args.paper,
                    "acceptance_credential": False,
                    "strict_closeout_required_for_acceptance": True,
                    "start_another_closeout": False,
                    "closeout_start_disposition": "already_running",
                    "active_execution": active_execution,
                    "actions": [],
                },
                indent=2,
                sort_keys=True,
            )
        )
        return 0
    (
        _prior_execution,
        early_execution_error,
        early_execution_namespace,
        early_execution_path,
    ) = effective_closeout_execution_state(ROOT, args.paper)
    if early_execution_error:
        status_argv = [
            "python3",
            "scripts/run_paper_closeout.py",
            "--paper",
            args.paper,
            "--status",
        ]
        recovery_action = {
            "id": "inspect_closeout_recovery",
            "state": "ready_now",
            "required": True,
            "argv": status_argv,
            "command": shlex.join(status_argv),
            "reason": early_execution_error,
        }
        print(
            json.dumps(
                {
                    "schema": 2,
                    "paper": args.paper,
                    "acceptance_credential": False,
                    "strict_closeout_required_for_acceptance": True,
                    "expensive_planning_deferred": True,
                    "execution_namespace": early_execution_namespace,
                    "execution_path": str(early_execution_path.relative_to(ROOT)),
                    "next_action": recovery_action,
                    "actions": [recovery_action],
                },
                indent=2,
                sort_keys=True,
            )
        )
        return 0

    # Module-byte drift is not proof that a paper's accepted declarations or
    # source semantics changed. The canonical validator owns both the exact-
    # byte fast path and strict Lean semantic recovery; no byte-level planner
    # shortcut may preempt it.
    terminal_plan = current_canonical_receipt_terminal_plan(folder)
    if terminal_plan is not None:
        print(json.dumps(terminal_plan, indent=2, sort_keys=True))
        return 0

    engine_error = runtime_engine_registration_error(ROOT)
    if engine_error:
        registration_action = {
            "id": "inspect_engine_registration",
            "state": "ready_now",
            "required": True,
            "reason": engine_error,
        }
        print(
            json.dumps(
                {
                    "schema": 2,
                    "paper": args.paper,
                    "acceptance_credential": False,
                    "strict_closeout_required_for_acceptance": True,
                    "expensive_planning_deferred": True,
                    "next_action": registration_action,
                    "actions": [registration_action],
                },
                indent=2,
                sort_keys=True,
            )
        )
        return 2

    paper_status, status_error = _paper_closeout_status_preflight(folder)
    if status_error:
        # Keep a status-stop response informative without opening source
        # artifacts.  Eligible papers use the one full static pass below,
        # rather than scanning the same Lean/report surface twice.
        static_readiness = static_closeout_readiness(
            folder,
            include_intake=False,
            require_terminal_documents=False,
        )
        print(
            json.dumps(
                {
                    "schema": 2,
                    "paper": args.paper,
                    "acceptance_credential": False,
                    "strict_closeout_required_for_acceptance": True,
                    "paper_status": paper_status,
                    "readiness_matrix": static_readiness,
                    "expensive_planning_deferred": True,
                    "next_action": {
                        "id": "resolve_paper_closeout_eligibility",
                        "state": "ready_now",
                        "required": True,
                        "reason": status_error,
                    },
                    "actions": [
                        {
                            "id": "resolve_paper_closeout_eligibility",
                            "state": "ready_now",
                            "required": True,
                            "reason": status_error,
                        }
                    ],
                },
                indent=2,
                sort_keys=True,
            )
        )
        return 0

    # An ineligible paper above does not pay the prospective intake's exact
    # source-artifact/atom scan. An eligible paper without a current accepted
    # graph gets exactly one full deterministic readiness pass before raw
    # evidence or cache state.
    static_readiness = static_closeout_readiness(
        folder,
        require_terminal_documents=False,
    )
    if not static_readiness["ready"]:
        print(
            json.dumps(
                {
                    "schema": 2,
                    "paper": args.paper,
                    "acceptance_credential": False,
                    "strict_closeout_required_for_acceptance": True,
                    "readiness_matrix": static_readiness,
                    "expensive_planning_deferred": True,
                    "next_action": {
                        "id": "resolve_static_closeout_blockers",
                        "state": "ready_now",
                        "reason": (
                            "finish the listed deterministic paper-local obligations "
                            "before hashing manifests or running semantic reuse"
                        ),
                    },
                    "actions": [],
                },
                indent=2,
                sort_keys=True,
            )
        )
        return 0

    # Reject the complete typed route/atom shape before scheduling Lean. The
    # prerequisite ledgers are intentionally absent at this phase because the
    # unified graph is what discovers and classifies their exact declaration
    # denominator. Their bindings are checked again under the strict default
    # immediately after reviewer issuance below.
    graph_input_preflight = v11_structural_graph_input_preflight(
        folder,
        require_prerequisite_ledger_bindings=False,
    )
    if (
        graph_input_preflight is not None
        and graph_input_preflight.get("current") is not True
    ):
        blockers = [
            str(item).strip()
            for item in graph_input_preflight.get("errors") or []
            if str(item).strip()
        ]
        action = {
            "id": "repair_typed_obligation_surface",
            "state": "ready_now",
            "reason": " ; ".join(blockers)
            or "the typed source/Spec graph input is incomplete",
        }
        print(
            json.dumps(
                {
                    "schema": 2,
                    "paper": args.paper,
                    "acceptance_credential": False,
                    "strict_closeout_required_for_acceptance": True,
                    "readiness_matrix": static_readiness,
                    "obligation_preflight": graph_input_preflight,
                    "expensive_planning_deferred": True,
                    "next_action": action,
                    "actions": [action],
                },
                indent=2,
                sort_keys=True,
            )
        )
        return 0

    try:
        planner_status_payload = json.loads(
            (folder / "status.json").read_text(encoding="utf-8")
        )
        planner_source_map_payload = json.loads(
            (folder / "audit" / "paper_statement_map.json").read_text(
                encoding="utf-8"
            )
        )
    except (OSError, UnicodeDecodeError, json.JSONDecodeError) as exc:
        repair_action = {
            "id": "repair_current_v11_context",
            "state": "ready_now",
            "required": True,
            "reason": "could not read the selected v11 control inputs: " + str(exc),
        }
        print(
            json.dumps(
                {
                    "schema": 2,
                    "paper": args.paper,
                    "acceptance_credential": False,
                    "requires_fresh_strict_closeout": True,
                    "readiness_matrix": static_readiness,
                    "current_protocol": "v11_graph_native",
                    "legacy_planner_consulted": False,
                    "expensive_planning_deferred": True,
                    "next_action": repair_action,
                    "actions": [repair_action],
                },
                indent=2,
                sort_keys=True,
            )
        )
        return 0
    if not isinstance(planner_status_payload, Mapping) or not isinstance(
        planner_source_map_payload, Mapping
    ):
        raise SystemExit("current v11 status and statement map must be objects")
    planner_requests_v11 = _raw_source_spec_screening_requested(
        folder,
        planner_status_payload,
        planner_source_map_payload,
    )
    if not planner_requests_v11:
        # Accepted historical receipts returned through the canonical-receipt
        # fast path above.  A paper without one must enter the single current
        # protocol; it may not execute a retired planner, adopt an old worker,
        # or manufacture a compatibility credential.
        print(
            json.dumps(
                current_protocol_migration_plan(args.paper, static_readiness),
                indent=2,
                sort_keys=True,
            )
        )
        return 0

    approval_projection_action = current_approved_review_context_projection_action(
        folder,
        planner_source_map_payload,
    )
    if approval_projection_action is not None:
        print(
            json.dumps(
                {
                    "schema": 2,
                    "paper": args.paper,
                    "acceptance_credential": False,
                    "strict_closeout_required_for_acceptance": True,
                    "readiness_matrix": static_readiness,
                    "current_protocol": "v11_graph_native",
                    "legacy_planner_consulted": False,
                    "expensive_planning_deferred": True,
                    "next_action": approval_projection_action,
                    "actions": [approval_projection_action],
                },
                indent=2,
                sort_keys=True,
            )
        )
        return 0

    inventory_action = current_source_inventory_candidate_review_action(
        folder,
        planner_source_map_payload,
    )
    if inventory_action is not None:
        print(
            json.dumps(
                {
                    "schema": 2,
                    "paper": args.paper,
                    "acceptance_credential": False,
                    "strict_closeout_required_for_acceptance": True,
                    "readiness_matrix": static_readiness,
                    "current_protocol": "v11_graph_native",
                    "legacy_planner_consulted": False,
                    "expensive_planning_deferred": True,
                    "next_action": inventory_action,
                    "actions": [inventory_action],
                },
                indent=2,
                sort_keys=True,
            )
        )
        return 0

    # Reject a malformed reviewer container before loading even the saved Lean
    # graph.  This grants no semantic credit; it merely preserves the cheapest
    # deterministic repair boundary.
    screening_preflight_errors = current_v11_saved_screening_preflight_errors(
        folder
    )
    if screening_preflight_errors:
        # A review queue depends on the portable Lean import closure.  Check
        # that small prerequisite before importing the graph/review engine;
        # an old screening plus an absent closure must not spend a full graph
        # acquisition merely to rediscover this deterministic first action.
        repair_action = current_v11_import_closure_action(folder)
        if repair_action is None:
            repair_action = current_v11_screening_repair_action(
                folder,
                screening_preflight_errors,
            )
        if repair_action.get("id") == "prepare_v11_lean_review_graph":
            # The graph producer requires the portable Lean import-closure
            # carrier.  A missing screening commonly reaches this branch on a
            # fresh paper, so ask the one prerequisite state machine for the
            # actual next action instead of emitting an impossible graph
            # command.  Malformed screening with an already prepared graph
            # still stops at its cheaper queue/metadata repair above.
            graph_stage = current_v11_prerequisite_stage(
                folder,
                status_payload=planner_status_payload,
                source_map_payload=planner_source_map_payload,
            )
            graph_action = graph_stage.action
            if graph_action is not None and graph_action.get("id") in {
                "record_current_lean_import_closure",
                "repair_v11_lean_review_graph",
                "prepare_v11_lean_review_graph",
            }:
                repair_action = graph_action
        print(
            json.dumps(
                {
                    "schema": 2,
                    "paper": args.paper,
                    "acceptance_credential": False,
                    "requires_fresh_strict_closeout": True,
                    "readiness_matrix": static_readiness,
                    "current_protocol": "v11_graph_native",
                    "screening_container_preflight": {
                        "current": False,
                        "errors": screening_preflight_errors,
                        "semantic_acceptance": False,
                    },
                    "legacy_planner_consulted": False,
                    "expensive_planning_deferred": True,
                    "next_action": repair_action,
                    "actions": [repair_action],
                },
                indent=2,
                sort_keys=True,
            )
        )
        return 0

    prerequisite_stage = current_v11_prerequisite_stage(
        folder,
        status_payload=planner_status_payload,
        source_map_payload=planner_source_map_payload,
    )
    prerequisite_action = prerequisite_stage.action
    if prerequisite_action is not None:
        print(
            json.dumps(
                {
                    "schema": 2,
                    "paper": args.paper,
                    "acceptance_credential": False,
                    "strict_closeout_required_for_acceptance": True,
                    "readiness_matrix": static_readiness,
                    "current_protocol": "v11_graph_native",
                    "legacy_planner_consulted": False,
                    "expensive_planning_deferred": True,
                    "next_action": prerequisite_action,
                    "actions": [prerequisite_action],
                },
                indent=2,
                sort_keys=True,
            )
        )
        return 0
    planner_evidence_context = prerequisite_stage.evidence_context

    # Reviewer ledgers now exist, so the same typed preflight can require their
    # exact graph bindings before any semantic acceptance check proceeds.
    obligation_preflight = v11_structural_graph_input_preflight(folder)
    if (
        obligation_preflight is not None
        and obligation_preflight.get("current") is not True
    ):
        blockers = [
            str(item).strip()
            for item in obligation_preflight.get("errors") or []
            if str(item).strip()
        ]
        action = {
            "id": "repair_typed_obligation_surface",
            "state": "ready_now",
            "reason": " ; ".join(blockers)
            or "the fresh source/Spec/theorem obligation surface is incomplete",
        }
        print(
            json.dumps(
                {
                    "schema": 2,
                    "paper": args.paper,
                    "acceptance_credential": False,
                    "strict_closeout_required_for_acceptance": True,
                    "readiness_matrix": static_readiness,
                    "obligation_preflight": obligation_preflight,
                    "expensive_planning_deferred": True,
                    "next_action": action,
                    "actions": [action],
                },
                indent=2,
                sort_keys=True,
            )
        )
        return 0

    if not bool(
        getattr(planner_evidence_context, "v11_lean_claim_graph_selected", False)
    ):
        repair_action = {
            "id": "repair_current_v11_context",
            "state": "ready_now",
            "required": True,
            "reason": (
                "the exact prerequisite planner did not retain the selected "
                "v11 Lean claim graph"
            ),
        }
        print(
            json.dumps(
                {
                    "schema": 2,
                    "paper": args.paper,
                    "acceptance_credential": False,
                    "requires_fresh_strict_closeout": True,
                    "readiness_matrix": static_readiness,
                    "current_protocol": "v11_graph_native",
                    "legacy_planner_consulted": False,
                    "expensive_planning_deferred": True,
                    "next_action": repair_action,
                    "actions": [repair_action],
                },
                indent=2,
                sort_keys=True,
            )
        )
        return 0

    # Persist the graph immediately after the operational semantic gate below.
    # This keeps one Lean acquisition reusable even when the semantic result is
    # a repair obligation.
    v11_lean_graph_persistence_error = ""

    # The selected graph-native route already owns one exact evidence
    # transaction. Project it directly before opening any historical
    # statement/coverage sidecar or dashboard-planner input. The transaction
    # snapshot, not a parallel v10 material list, is the mutation authority.
    if planner_evidence_context is not None:
        if not isinstance(planner_source_map_payload, Mapping):
            raise SystemExit("current v11 statement map is not an object")
        mode, mode_error = source_coverage_mode_from_map(
            planner_source_map_payload
        )
        if mode_error:
            print(
                json.dumps(
                    {
                        "schema": 2,
                        "paper": args.paper,
                        "acceptance_credential": False,
                        "requires_fresh_strict_closeout": True,
                        "cache_reusable": False,
                        "invalidation_reasons": [
                            f"current source coverage mode is invalid: {mode_error}"
                        ],
                        "actions": [],
                    },
                    indent=2,
                    sort_keys=True,
                )
            )
            return 2
        screening_path_suffix = "audit/v11_raw_source_spec_screening.json"
        current_screening_findings = current_v11_raw_source_spec_screening_findings(
            ROOT,
            folder,
            context=planner_evidence_context,
        )
        current_screening_errors = [
            finding.message
            for finding in current_screening_findings
            if str(finding.path).replace("\\", "/").endswith(
                screening_path_suffix
            )
        ]
        if current_screening_errors:
            # The semantic validator has consumed the builder-issued graph.
            # Materialize that exact graph and packet projection before
            # scheduling the changed-row queue, so repairing a source/Spec
            # verdict never triggers a second Lean discovery pass.
            v11_lean_graph_persistence_error = persist_v11_operational_lean_graph(
                folder,
                planner_evidence_context,
            )
            repair_action = current_v11_screening_repair_action(
                folder,
                current_screening_errors,
            )
            blocked_plan: dict[str, Any] = {
                "schema": 2,
                "paper": args.paper,
                "acceptance_credential": False,
                "requires_fresh_strict_closeout": True,
                "readiness_matrix": static_readiness,
                "current_protocol": "v11_graph_native",
                "invalidation_reasons": current_screening_errors,
                "legacy_planner_consulted": False,
                "expensive_planning_deferred": True,
                "next_action": repair_action,
                "actions": [repair_action],
            }
            if v11_lean_graph_persistence_error:
                blocked_plan["v11_lean_review_graph_checkpoint_error"] = (
                    v11_lean_graph_persistence_error
                )
            print(json.dumps(blocked_plan, indent=2, sort_keys=True))
            return 0
        live_v11_acquisition, planner_v11_live_errors = (
            current_v11_live_lean_operational_plan(
                folder,
                source_map=planner_source_map_payload,
                evidence_context=planner_evidence_context,
            )
        )
        v11_lean_graph_persistence_error = persist_v11_operational_lean_graph(
            folder,
            planner_evidence_context,
        )
        if live_v11_acquisition is not None:
            live_v11_plan = live_v11_acquisition.plan
            live_v11_plan = finalize_operational_plan(
                live_v11_plan,
                folder=folder,
                source_coverage_mode=mode,
                execution_path=execution_path,
                static_readiness=static_readiness,
                publication_inputs=live_v11_acquisition.publication_inputs,
                evidence_context=planner_evidence_context,
                v11_lean_graph_persistence_error=(
                    v11_lean_graph_persistence_error
                ),
            )
            output_plan = operator_plan_for_output(
                live_v11_plan, args.paper, all_items=args.all_items
            )
            print(json.dumps(output_plan, indent=2, sort_keys=True))
            return 0
        repair_errors = [
            str(error).strip()
            for error in planner_v11_live_errors
            if str(error).strip()
        ]
        repair_action = {
            "id": "repair_current_v11_audit",
            "state": "ready_now",
            "required": True,
            "reason": "; ".join(repair_errors)
            or "the selected v11 graph-native audit is incomplete",
        }
        blocked_plan: dict[str, Any] = {
            "schema": 2,
            "paper": args.paper,
            "acceptance_credential": False,
            "requires_fresh_strict_closeout": True,
            "readiness_matrix": static_readiness,
            "current_protocol": "v11_graph_native",
            "invalidation_reasons": repair_errors,
            "legacy_planner_consulted": False,
            "expensive_planning_deferred": True,
            "next_action": repair_action,
            "actions": [repair_action],
        }
        if v11_lean_graph_persistence_error:
            blocked_plan["v11_lean_review_graph_checkpoint_error"] = (
                v11_lean_graph_persistence_error
            )
        print(json.dumps(blocked_plan, indent=2, sort_keys=True))
        return 0

if __name__ == "__main__":
    raise SystemExit(main())
