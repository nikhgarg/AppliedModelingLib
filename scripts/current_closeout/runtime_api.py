#!/usr/bin/env python3
"""Small current-only API consumed by the strict closeout executor.

This module is the boundary between the generic stage orchestrator and the
current graph-native validators.  It deliberately does not import
``audit_repository`` or any historical conclusion/status implementation.
Legacy closeout remains readable through its historical entrypoints, while a
selected current closeout receives exactly one builder-issued v11 context,
one Lean semantic surface, one primary verdict, one evidence verdict, one
focused build, and one final mutation check.
"""

from __future__ import annotations

import hashlib
import json
import re
import subprocess
from collections.abc import Mapping, MutableMapping
from dataclasses import dataclass
from pathlib import Path
from typing import Any

from scripts.closeout_document_gates import closeout_document_hard_errors
from scripts.current_closeout.evidence_acceptance import (
    accepted_current_v11_evidence_integrity,
)
from scripts.current_closeout.evidence_gate import run_current_evidence_gate
from scripts.current_closeout.evidence_transaction import (
    CurrentV11EvidenceSnapshotRoot,
)
from scripts.current_closeout.input_mutation import current_evidence_input_mutations
from scripts.current_closeout.primary_gate_transaction import (
    evaluate_and_accept_current_v11_primary_gate,
)
from scripts.current_closeout.semantic_review import (
    current_v11_semantic_review_result,
)
from scripts.evidence_run_context import V11EvidenceRunContext
from scripts.lean_process_diagnostics import (
    bounded_lean_diagnostic_excerpt,
    lean_diagnostic_failure_reason,
)
from scripts.paper_module_elaboration import (
    PaperModuleElaborationError,
    rehashed_module_build_command,
    tracked_paper_module_sources,
)

ROOT = Path(__file__).resolve().parents[2]
PAPERS = ROOT / "papers"
AUDIT_CONFIG = PAPERS / "audit_config.json"

_DAG_REPORT_HEADING_RE = re.compile(
    r"(?mi)^##+\s+(?:\d+\.\s*)?DAG\s+(?:Audit|Status)\b"
)
_VALIDATION_HEADING_RE = re.compile(
    r"(?mi)^##+\s+(?:\d+\.\s*)?(?:Validation Checks|Validation Commands)\b"
)
_AUDIT_COMMANDS_HEADING_RE = re.compile(
    r"(?mi)^##+\s+(?:\d+\.\s*)?(?:Commands|Validation Commands)\b"
)


@dataclass(frozen=True)
class Finding:
    """One repository-facing current-closeout finding."""

    severity: str
    path: Path
    message: str

    def format(self) -> str:
        try:
            rendered = self.path.resolve().relative_to(ROOT.resolve())
        except (OSError, RuntimeError, ValueError):
            rendered = self.path
        return f"[{self.severity}] {rendered}: {self.message}"


def load_audit_config() -> dict[str, object]:
    """Read the exact process-start audit configuration."""

    if not AUDIT_CONFIG.exists():
        return {}
    payload = json.loads(AUDIT_CONFIG.read_text(encoding="utf-8"))
    if not isinstance(payload, dict):
        raise TypeError("papers/audit_config.json should contain an object")
    schema = payload.get("schema")
    if isinstance(schema, bool) or schema != 1:
        raise ValueError("papers/audit_config.json should use schema 1")
    return payload


AUDIT_CONFIG_PAYLOAD = load_audit_config()


def _path(value: object) -> Path:
    path = Path(str(value))
    return path if path.is_absolute() else ROOT / path


def _convert_findings(
    findings: object,
    *,
    paper_id: str,
    label: str,
) -> list[Finding]:
    converted: list[Finding] = []
    if not isinstance(findings, (tuple, list)):
        return [
            Finding(
                "ERROR",
                PAPERS / paper_id / "status.json",
                f"`{paper_id}` {label} returned a malformed finding set",
            )
        ]
    for finding in findings:
        converted.append(
            Finding(
                str(getattr(finding, "severity", "ERROR")),
                _path(getattr(finding, "path", PAPERS / paper_id / "status.json")),
                f"`{paper_id}` {label}: {getattr(finding, 'message', finding)}",
            )
        )
    return converted


class PaperCloseoutRunContext:
    """Minimal current-v11 transaction view required by the stage executor."""

    __slots__ = (
        "build_input_provider",
        "evidence_context",
        "folder",
        "paper_id",
        "v11_direct_semantic_review_current",
        "v11_direct_semantic_review_error",
        "v11_lean_review_surface",
    )

    @classmethod
    def from_exact_evidence_context(
        cls,
        paper_id: str,
        folder: Path,
        *,
        evidence_context: object,
    ) -> PaperCloseoutRunContext:
        resolved = folder.resolve()
        if (
            not isinstance(evidence_context, V11EvidenceRunContext)
            or not evidence_context.issued_by_builder
            or not evidence_context.v11_lean_claim_graph_selected
            or evidence_context.folder != resolved
            or resolved != (PAPERS / paper_id).resolve()
        ):
            raise ValueError(
                "current closeout run context requires its exact builder-issued "
                "v11 evidence transaction"
            )
        semantic = current_v11_semantic_review_result(
            ROOT,
            resolved,
            context=evidence_context,
        )
        instance = cls()
        instance.paper_id = paper_id
        instance.folder = resolved
        instance.evidence_context = evidence_context
        instance.v11_direct_semantic_review_current = (
            semantic.semantic_review_current
        )
        if semantic.selection_error:
            error = semantic.selection_error
        elif semantic.findings:
            error = semantic.findings[0].message
        elif semantic.surface is None:
            error = "current Lean semantic surface is unavailable"
        else:
            error = ""
        instance.v11_direct_semantic_review_error = error
        instance.v11_lean_review_surface = semantic.surface
        instance.build_input_provider = (
            semantic.surface.build_input_provider
            if semantic.surface is not None
            else None
        )
        return instance

    @property
    def issued_by_builder(self) -> bool:
        return bool(
            isinstance(self.evidence_context, V11EvidenceRunContext)
            and self.evidence_context.issued_by_builder
            and self.evidence_context.folder == self.folder
        )

    @property
    def selected_v11_closeout(self) -> bool:
        return self.issued_by_builder

    @property
    def current_v11_closeout(self) -> bool:
        return self.issued_by_builder and self.v11_direct_semantic_review_current

    def evaluate_and_accept_current_v11_primary_gate(self) -> tuple[object, object]:
        return evaluate_and_accept_current_v11_primary_gate(
            ROOT,
            self.folder,
            context=self.evidence_context,
        )

    def publish_staged_strict_v11_source_record_judgment_handoff(self) -> bool:
        raise RuntimeError("current closeout has no legacy source-record handoff")

    def diagnostics(self) -> dict[str, int]:
        surface = self.v11_lean_review_surface
        return {
            "paper_semantic_target_count": len(
                getattr(surface, "paper_semantic_targets", {})
            ),
            "library_semantic_target_count": len(
                getattr(surface, "library_semantic_targets", {})
            ),
            "paper_prerequisite_count": len(
                getattr(surface, "paper_prerequisites", ())
            ),
            "library_prerequisite_count": len(
                getattr(surface, "library_prerequisites", ())
            ),
        }


def build_paper_closeout_evidence_context(
    paper_id: str,
    *,
    diagnostics: MutableMapping[str, int] | None = None,
    operational_plan_receipt: Mapping[str, object] | None = None,
) -> V11EvidenceRunContext:
    """Acquire only the current graph-native transaction; never fall back."""

    if diagnostics is not None:
        diagnostics["evidence_contexts_built"] = (
            diagnostics.get("evidence_contexts_built", 0) + 1
        )
    graph_reference = (
        operational_plan_receipt.get("v11_lean_review_graph")
        if isinstance(operational_plan_receipt, Mapping)
        else None
    )
    root = CurrentV11EvidenceSnapshotRoot.acquire(
        PAPERS / paper_id,
        repository_root=ROOT,
    )
    if not root.v11_selected:
        raise ValueError(
            "paper does not select the current graph-native closeout protocol"
        )
    return root.build_v11(
        graph_reference if isinstance(graph_reference, Mapping) else None
    )




def paper_closeout_evidence_context_prebuild_findings(
    paper_id: str,
    evidence_context: object,
    *,
    run_context: PaperCloseoutRunContext | None = None,
) -> list[Finding]:
    """Stop before the build unless the selected semantic verdict is current."""

    if (
        not isinstance(evidence_context, V11EvidenceRunContext)
        or run_context is None
        or run_context.evidence_context is not evidence_context
        or not run_context.selected_v11_closeout
    ):
        return [
            Finding(
                "ERROR",
                PAPERS / paper_id / "status.json",
                f"`{paper_id}` prebuild gate requires one exact current run context",
            )
        ]
    if run_context.current_v11_closeout:
        return []
    detail = run_context.v11_direct_semantic_review_error.strip()
    return [
        Finding(
            "ERROR",
            PAPERS / paper_id / "status.json",
            f"`{paper_id}` selected current semantic lane is not current: "
            + (detail or "the exact semantic-review conjunction did not pass"),
        )
    ]


def paper_closeout_evidence_integrity_findings(
    paper_id: str,
    *,
    require_source_bytes: bool,
    context: object | None = None,
    diagnostics: MutableMapping[str, int] | None = None,
) -> list[Finding]:
    """Run the complete current evidence conjunction in-process."""

    if not isinstance(context, V11EvidenceRunContext):
        return [
            Finding(
                "ERROR",
                PAPERS / paper_id / "status.json",
                f"`{paper_id}` evidence integrity requires its current transaction",
            )
        ]
    raw = run_current_evidence_gate(
        repository_root=ROOT,
        paper_id=paper_id,
        release=False,
        require_source_bytes=require_source_bytes,
        diagnostics=diagnostics,
        context=context,
    )
    return _convert_findings(raw, paper_id=paper_id, label="evidence integrity")


def paper_closeout_conclusion_provenance_findings(
    paper_id: str,
    *,
    theorem_realization_component_prevalidated: bool = False,
    context: object | None = None,
) -> list[Finding]:
    """Require the exact current evidence capability; do not rerun legacy logic."""

    if (
        theorem_realization_component_prevalidated
        and isinstance(context, V11EvidenceRunContext)
        and accepted_current_v11_evidence_integrity(context) is not None
    ):
        return []
    return [
        Finding(
            "ERROR",
            PAPERS / paper_id / "PaperInterface.lean",
            f"`{paper_id}` conclusion provenance lacks the exact accepted current "
            "primary-and-evidence capability",
        )
    ]


def paper_closeout_context_mutation_findings(
    context: object,
    *,
    diagnostics: MutableMapping[str, int] | None = None,
    build_input_provider: object | None = None,
) -> list[Finding]:
    """Check the exact current snapshots and Lean build inputs exactly once."""

    if not isinstance(context, V11EvidenceRunContext) or not context.issued_by_builder:
        return [
            Finding(
                "ERROR",
                PAPERS,
                "current evidence transaction was not issued by its snapshot builder",
            )
        ]
    try:
        changed = current_evidence_input_mutations(context)
    except ValueError as exc:
        return [Finding("ERROR", context.folder / "status.json", str(exc))]
    findings: list[Finding] = []
    if changed:
        if diagnostics is not None:
            diagnostics["watched_input_mutations"] = (
                diagnostics.get("watched_input_mutations", 0) + 1
            )
        rendered = []
        for path in changed[:5]:
            try:
                rendered.append(path.resolve().relative_to(ROOT).as_posix())
            except (OSError, RuntimeError, ValueError):
                rendered.append(str(path))
        findings.append(
            Finding(
                "ERROR",
                context.folder / "status.json",
                "evidence inputs changed during the current closeout transaction; "
                "discard all run-scoped authorization results (exact inputs changed: "
                + ", ".join(rendered)
                + ("; ..." if len(changed) > 5 else "")
                + ")",
            )
        )
    finalize = getattr(build_input_provider, "finalize_unchanged", None)
    if build_input_provider is not None and (
        not callable(finalize) or finalize() is not True
    ):
        findings.append(
            Finding(
                "ERROR",
                ROOT / "lean-toolchain",
                "repository Lean build/import inputs changed during the paper "
                "closeout transaction; discard every graph-derived result",
            )
        )
    return findings


def closeout_transaction_input_sha256(
    run_context: PaperCloseoutRunContext | None,
) -> str:
    """Return operational input telemetry without granting acceptance."""

    if run_context is None:
        return ""
    context = run_context.evidence_context
    snapshots = [
        {
            "path": (
                snapshot.path.resolve().relative_to(ROOT).as_posix()
                if ROOT in snapshot.path.resolve().parents
                else str(snapshot.path)
            ),
            "sha256": snapshot.sha256,
        }
        for snapshot in context.input_snapshots
    ]
    material = {
        # This is current-v11 operational telemetry.  Legacy source-record
        # watch digests are deliberately absent from the current typed
        # transaction and must never become a hidden runtime dependency here.
        "schema": 2,
        "paper": run_context.paper_id,
        "json_snapshots": sorted(snapshots, key=lambda item: item["path"]),
    }
    return hashlib.sha256(
        json.dumps(
            material,
            ensure_ascii=True,
            sort_keys=True,
            separators=(",", ":"),
        ).encode("utf-8")
    ).hexdigest()


def check_paper_root_build_closeout(paper_id: str) -> list[Finding]:
    """Rehash and build every tracked paper module in one Lake transaction."""

    try:
        sources = tracked_paper_module_sources(ROOT, paper_id)
        command = rehashed_module_build_command(
            ROOT,
            sources,
            single_threaded=True,
        )
    except PaperModuleElaborationError as exc:
        return [
            Finding(
                "ERROR",
                PAPERS / paper_id / "PaperInterface.lean",
                f"`{paper_id}` paper-module inventory is invalid: {exc}",
            )
        ]
    try:
        proc = subprocess.run(
            command,
            cwd=ROOT,
            check=False,
            capture_output=True,
            text=True,
            timeout=900,
        )
    except (OSError, subprocess.TimeoutExpired) as exc:
        return [
            Finding(
                "ERROR",
                PAPERS / paper_id / "PaperInterface.lean",
                f"`{paper_id}` complete tracked-module build could not run: {exc}",
            )
        ]
    diagnostic_failure = lean_diagnostic_failure_reason(proc.stdout, proc.stderr)
    if proc.returncode == 0 and not diagnostic_failure:
        return []
    reason = diagnostic_failure or f"Lake exited {proc.returncode}"
    excerpt = bounded_lean_diagnostic_excerpt(proc.stdout, proc.stderr)
    if excerpt:
        reason += f": {excerpt}"
    return [
        Finding(
            "ERROR",
            PAPERS / paper_id / "PaperInterface.lean",
            f"`{paper_id}` complete tracked-module build failed: {reason}",
        )
    ]


def _read_text(path: Path) -> str:
    try:
        return path.read_text(encoding="utf-8")
    except OSError:
        return ""


def _paper_file(folder: Path, preferred: str, legacy: str) -> Path:
    preferred_path = folder / preferred
    if preferred_path.exists():
        return preferred_path
    legacy_path = folder / legacy
    return legacy_path if legacy_path.exists() else preferred_path


def check_dag_and_validation_report_closeout(
    include_active: bool,
    paper_filter: str | None = None,
    *,
    force_selected_closeout: bool = False,
    final_holistic_surface_sha256: str = "",
    all_selected_semantic_review_sha256: str | None = None,
    final_holistic_review_policy_assurance: Mapping[str, object] | None = None,
) -> list[Finding]:
    """Validate current closeout documents for the exact selected paper."""

    del include_active, force_selected_closeout
    if not paper_filter:
        return [Finding("ERROR", PAPERS, "paper closeout requires one paper")]
    folder = PAPERS / paper_filter
    report = folder / "FINAL_VALIDATION_REPORT.md"
    post_audit = _paper_file(
        folder,
        "docs/POST_FORMALIZATION_AUDIT.md",
        "POST_FORMALIZATION_AUDIT.md",
    )
    dag_tex = _paper_file(folder, "docs/DependencyDAG.tex", "DependencyDAG.tex")
    dag_pdf = _paper_file(folder, "docs/DependencyDAG.pdf", "DependencyDAG.pdf")
    agent_audit = folder / "docs" / "AGENT_SOURCE_AUDIT.md"
    findings = [
        Finding("ERROR", error.path, error.message)
        for error in closeout_document_hard_errors(
            folder,
            corrected_scope_current=False,
            final_holistic_required=True,
            require_visual_dag_inspection=True,
            final_holistic_surface_sha256=final_holistic_surface_sha256,
            all_selected_semantic_review_sha256=(
                all_selected_semantic_review_sha256
            ),
            final_holistic_review_policy_assurance=(
                final_holistic_review_policy_assurance
            ),
            post_formalization_audit=post_audit,
        )
    ]
    if not report.exists():
        findings.append(
            Finding(
                "ERROR",
                folder,
                "completed paper is missing `FINAL_VALIDATION_REPORT.md`",
            )
        )
    report_text = _read_text(report)
    if report_text:
        if not _DAG_REPORT_HEADING_RE.search(report_text):
            findings.append(
                Finding("WARN", report, "final validation report lacks a DAG section")
            )
        if not _VALIDATION_HEADING_RE.search(report_text):
            findings.append(
                Finding(
                    "WARN",
                    report,
                    "final validation report lacks a validation-commands section",
                )
            )
        for artifact in ("DependencyDAG.tex", "DependencyDAG.pdf"):
            if artifact not in report_text:
                findings.append(
                    Finding(
                        "WARN",
                        report,
                        f"final validation report should name `{artifact}`",
                    )
                )
        if not (
            "scripts/run_paper_closeout.py" in report_text
            or (
                f"--paper {paper_filter}" in report_text
                and "scripts/audit_repository.py" in report_text
            )
        ):
            findings.append(
                Finding(
                    "WARN",
                    report,
                    "final validation report should record the targeted closeout command",
                )
            )
    agent_text = _read_text(agent_audit)
    for heading in (
        "Source Inventory",
        "Lean Interface Comparison",
        "Machine Audit Results",
        "Findings",
    ):
        if agent_text and not re.search(
            rf"^##\s+{re.escape(heading)}\s*$", agent_text, re.MULTILINE
        ):
            findings.append(
                Finding(
                    "WARN",
                    agent_audit,
                    f"`docs/AGENT_SOURCE_AUDIT.md` should include `{heading}`",
                )
            )
    post_text = _read_text(post_audit)
    if post_text:
        if not _DAG_REPORT_HEADING_RE.search(post_text):
            findings.append(
                Finding("WARN", post_audit, "post-formalization audit lacks a DAG section")
            )
        if not _AUDIT_COMMANDS_HEADING_RE.search(post_text):
            findings.append(
                Finding(
                    "WARN",
                    post_audit,
                    "post-formalization audit lacks a commands section",
                )
            )
        for artifact in (
            "FINAL_VALIDATION_REPORT.md",
            "DependencyDAG.tex",
            "DependencyDAG.pdf",
        ):
            if artifact not in post_text:
                findings.append(
                    Finding(
                        "WARN",
                        post_audit,
                        f"post-formalization audit should name `{artifact}`",
                    )
                )
        if not (
            "scripts/run_paper_closeout.py" in post_text
            or (
                f"--paper {paper_filter}" in post_text
                and "scripts/audit_repository.py" in post_text
            )
        ):
            findings.append(
                Finding(
                    "WARN",
                    post_audit,
                    "post-formalization audit should record the targeted closeout command",
                )
            )
    if not dag_pdf.exists():
        findings.append(
            Finding(
                "ERROR",
                dag_pdf,
                "completed paper is missing rendered `DependencyDAG.pdf`",
            )
        )
    elif dag_tex.exists() and dag_pdf.stat().st_mtime + 1 < dag_tex.stat().st_mtime:
        findings.append(
            Finding(
                "WARN",
                dag_pdf,
                "`DependencyDAG.pdf` is older than `DependencyDAG.tex`",
            )
        )
    return findings


def check_machine_paper_status(**_: Any) -> list[Finding]:
    """Fail if the current-only API is accidentally routed into legacy status."""

    raise RuntimeError("selected current closeout cannot execute legacy paper status")
