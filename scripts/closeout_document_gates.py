#!/usr/bin/env python3
"""Shared deterministic document gates for paper closeout.

The planner may use these checks to avoid work that the strict closeout would
unconditionally reject.  They are never acceptance evidence: the strict
transaction still rereads the same files and validates all semantic and Lean
inputs at its final boundary.
"""

from __future__ import annotations

import datetime as dt
import re
from collections.abc import Mapping
from dataclasses import dataclass
from pathlib import Path

from scripts.current_closeout.review_surface import (
    PACKET_LEAN_CACHE_NAME,
    SOURCE_MAP_NAME,
    _read_json,
    packet_lean_cache_missing_stages,
    prepared_review_surface,
)
from scripts.human_review_packet_renderer import PACKET_NAME, render_packet
from scripts.report_memo_coverage import COVERAGE_PATH, report_memo_coverage_errors
from scripts.final_validation_report_sections import final_report_section_errors
from scripts.human_result_label_guard import reader_facing_result_label_errors
from scripts.final_adversarial_review_panel import (
    audit_text_attestation_errors,
    final_adversarial_review_panel_errors,
)

PACKET_TEMPLATE_PATH = Path(__file__).with_name("templates") / "HUMAN_REVIEW_PACKET.tex.in"

from scripts.approved_review_context_report import (
    current_approved_review_context_report_errors,
)

AGENT_SOURCE_AUDIT_RELATIVE_PATH = Path("docs/AGENT_SOURCE_AUDIT.md")
FINAL_VALIDATION_REPORT_NAME = "FINAL_VALIDATION_REPORT.md"
POST_FORMALIZATION_AUDIT_RELATIVE_PATH = Path("docs/POST_FORMALIZATION_AUDIT.md")

STALE_PLACEHOLDER_RE = re.compile(
    r"(?mi)"
    r"^\s*-\s*(?:Rendered artifact|Topology|Layout)\s*:\s*not checked\s*$|"
    r"^\s*-\s*Not run\.\s*$|"
    r"\b(?:TODO|TBD|to be filled|not yet rendered|not inspected)\b"
)
_VISUAL_DAG_INSPECTION_RE = re.compile(
    r"(?is)(?:"
    r"\bvisual(?:ly)?\b.{0,80}\b(?:inspect(?:ed|ion)?|check(?:ed|ing)?)\b|"
    r"\b(?:inspect(?:ed|ion)?|check(?:ed|ing)?)\b.{0,80}\bvisual(?:ly)?\b|"
    r"\b(?:no|non[- ]?)\b.{0,50}\b(?:overlap|clipping)\b"
    r")"
)
_DAG_AUDIT_HEADING_RE = re.compile(
    r"(?mi)^(#{2,6})\s+(?:\d+\.\s*)?DAG\s+(?:Audit|Status)\b[^\n]*$"
)
_MARKDOWN_HEADING_RE = re.compile(r"(?m)^(#{1,6})\s+[^\n]+$")


@dataclass(frozen=True)
class CloseoutDocumentHardError:
    """One strict ERROR-class document condition, with its owning path."""

    path: Path
    message: str


def _dag_audit_section(report_text: str) -> str:
    """Return the report's DAG section, including nested subsections only."""

    heading = _DAG_AUDIT_HEADING_RE.search(report_text)
    if heading is None:
        return ""
    heading_level = len(heading.group(1))
    end = len(report_text)
    for candidate in _MARKDOWN_HEADING_RE.finditer(report_text, heading.end()):
        if len(candidate.group(1)) <= heading_level:
            end = candidate.start()
            break
    return report_text[heading.start():end]


def final_holistic_audit_hard_errors(
    folder: Path,
    *,
    target_surface_identity: str = "",
    require_surface_binding: bool = False,
    allow_historical_missing_scope: bool = False,
    review_policy_assurance: Mapping[str, object] | None = None,
) -> list[CloseoutDocumentHardError]:
    """Validate an independently completed final audit against one surface.

    The surface identity authenticates the selected source-to-Lean and proof
    comparison inputs.  It intentionally excludes operational scheduling
    inputs.  The required ``complete_current_surface`` attestation separately
    records that each independent reviewer read the complete policy-selected
    terminal comparison surface and human-facing artifacts; a bounded repair
    recheck cannot stand in for that terminal review.

    Only an authenticated accepted graph whose exact assurance matches a frozen
    schema-1 preimage may read a report without the later scope-marker spelling.
    This preserves its original PASS and exact target contract; an explicit
    bounded, unknown, or conflicting scope is never accepted in that mode.
    Fresh planner/finalizer callers retain the strict default.
    """

    if review_policy_assurance is not None:
        return [
            CloseoutDocumentHardError(finding.path, finding.message)
            for finding in final_adversarial_review_panel_errors(
                folder,
                target_surface_identity=target_surface_identity,
                review_policy_assurance=review_policy_assurance,
            )
        ]

    agent_source_audit = folder / AGENT_SOURCE_AUDIT_RELATIVE_PATH
    if not agent_source_audit.is_file():
        return [
            CloseoutDocumentHardError(
                agent_source_audit,
                "completed paper is missing `docs/AGENT_SOURCE_AUDIT.md` "
                "source-first holistic audit",
            )
        ]

    try:
        agent_audit_text = agent_source_audit.read_text(encoding="utf-8")
    except OSError as exc:
        return [
            CloseoutDocumentHardError(
                agent_source_audit,
                "completed-paper source-first holistic audit is unreadable: "
                + str(exc),
            )
        ]

    return [
        CloseoutDocumentHardError(
            agent_source_audit,
            "`docs/AGENT_SOURCE_AUDIT.md` " + message,
        )
        for message in audit_text_attestation_errors(
            agent_audit_text,
            target_surface_identity=target_surface_identity,
            require_surface_binding=require_surface_binding,
            allow_historical_missing_scope=allow_historical_missing_scope,
        )
    ]


def closeout_document_hard_errors(
    folder: Path,
    *,
    corrected_scope_current: bool,
    final_holistic_required: bool = False,
    check_final_holistic: bool = True,
    require_visual_dag_inspection: bool = False,
    final_holistic_surface_sha256: str = "",
    all_selected_semantic_review_sha256: str | None = None,
    final_holistic_review_policy_assurance: Mapping[str, object] | None = None,
    post_formalization_audit: Path | None = None,
) -> list[CloseoutDocumentHardError]:
    """Return strict ERROR-class document failures for one paper.

    ``corrected_scope_current`` must be the evidence-gate result used by the
    caller. ``post_formalization_audit`` permits the strict legacy-reader path
    while the planner uses the organized default. The corrected-scope exception
    applies only to a historical source-first audit requirement. A current
    closeout sets ``final_holistic_required`` and cannot use that exception.
    The planner may set ``check_final_holistic=False`` only while it prepares
    the semantic surface; the strict worker supplies its frozen surface identity.
    No corrected-scope result suppresses stale template text in
    researcher-facing reports. ``require_visual_dag_inspection`` is used only
    at the terminal-document boundary, after the semantic graph and focused
    build are current; it must not make draft documentation an early audit
    prerequisite.
    """

    errors: list[CloseoutDocumentHardError] = []
    report = folder / FINAL_VALIDATION_REPORT_NAME
    post_audit = post_formalization_audit or (
        folder / POST_FORMALIZATION_AUDIT_RELATIVE_PATH
    )
    if report.is_file():
        try:
            report_text = report.read_text(encoding="utf-8")
        except OSError as exc:
            errors.append(
                CloseoutDocumentHardError(
                    report,
                    "completed-paper final validation report is unreadable: " + str(exc),
                )
            )
        else:
            if require_visual_dag_inspection:
                for message in final_report_section_errors(report_text):
                    errors.append(CloseoutDocumentHardError(report, message))
                for message in reader_facing_result_label_errors(
                    folder, report_text=report_text
                ):
                    errors.append(CloseoutDocumentHardError(report, message))
            if STALE_PLACEHOLDER_RE.search(report_text):
                errors.append(
                    CloseoutDocumentHardError(
                        report,
                        "completed-paper final validation report still contains stale "
                        "placeholder audit language",
                    )
                )
            for message in current_approved_review_context_report_errors(folder):
                errors.append(
                    CloseoutDocumentHardError(
                        report,
                        "settled review context: " + message,
                    )
                )
            if (
                require_visual_dag_inspection
                and not _VISUAL_DAG_INSPECTION_RE.search(
                    _dag_audit_section(report_text)
                )
            ):
                errors.append(
                    CloseoutDocumentHardError(
                        report,
                        "completed-paper final validation report must record a visual "
                        "inspection of the rendered dependency DAG in its `DAG Audit` "
                        "or `DAG Status` section",
                    )
                )

    if require_visual_dag_inspection:
        semantic_basis = (
            all_selected_semantic_review_sha256
            if final_holistic_required
            else None
        )
        for message in report_memo_coverage_errors(
            folder,
            expected_all_selected_semantic_review_sha256=semantic_basis,
        ):
            errors.append(
                CloseoutDocumentHardError(
                    folder / COVERAGE_PATH,
                    "report clarification coverage: " + message,
                )
            )
        for packet_error in current_human_review_packet_errors(folder):
            errors.append(
                CloseoutDocumentHardError(
                    folder / "docs" / "HUMAN_REVIEW_PACKET.tex",
                    "human-review packet: " + packet_error,
                )
            )

    if post_audit.is_file():
        try:
            post_audit_text = post_audit.read_text(encoding="utf-8")
        except OSError as exc:
            errors.append(
                CloseoutDocumentHardError(
                    post_audit,
                    "completed-paper post-formalization audit is unreadable: " + str(exc),
                )
            )
        else:
            if STALE_PLACEHOLDER_RE.search(post_audit_text):
                errors.append(
                    CloseoutDocumentHardError(
                        post_audit,
                        "completed-paper post-formalization audit still contains stale "
                        "placeholder audit language",
                    )
                )

    if not check_final_holistic:
        return errors
    if corrected_scope_current and not final_holistic_required:
        return errors
    errors.extend(
        final_holistic_audit_hard_errors(
            folder,
            target_surface_identity=(
                final_holistic_surface_sha256 if final_holistic_required else ""
            ),
            require_surface_binding=final_holistic_required,
            review_policy_assurance=final_holistic_review_policy_assurance,
        )
    )
    return errors


def _packet_tex_currentness_text(tex: str) -> str:
    """Normalize presentation metadata that is intentionally non-semantic.

    Regenerating a packet on a later calendar date must not reopen an otherwise
    unchanged closeout.  The renderer's date is useful to a reader, but it is
    not part of the authenticated review surface.  All substantive packet text
    remains byte-compared after trimming only trailing horizontal whitespace.
    """

    lines: list[str] = []
    for raw_line in tex.split("\n"):
        line = raw_line.rstrip(" \t")
        if line.startswith("\\textbf{Generated:} "):
            suffix = r"\\" if line.endswith(r"\\") else ""
            line = r"\textbf{Generated:} <date>" + suffix
        lines.append(line)
    return "\n".join(lines)


def current_human_review_packet_errors(paper_dir: Path) -> tuple[str, ...]:
    """Return presentation-only reasons the committed review packet is stale.

    The closeout planner calls this only after the current semantic graph and
    reviewer ledgers are stable.  It never launches Lean: cache currentness is
    checked against the already saved graph, and the TeX comparison consumes
    that same authenticated presentation surface.  The PDF remains a rendered
    human artifact rather than audit evidence, but it must be present alongside
    the exact current TeX.
    """

    required = (
        paper_dir / PACKET_LEAN_CACHE_NAME,
        paper_dir / "docs" / f"{PACKET_NAME}.tex",
        paper_dir / "docs" / f"{PACKET_NAME}.pdf",
    )
    errors = [
        f"{path.relative_to(paper_dir).as_posix()}: missing human-review packet artifact"
        for path in required
        if not path.is_file()
    ]
    source_map_path = paper_dir / SOURCE_MAP_NAME
    if not source_map_path.is_file():
        errors.append(f"{SOURCE_MAP_NAME}: missing canonical source map")
        return tuple(errors)
    try:
        source_map = _read_json(source_map_path)
    except ValueError as exc:
        errors.append(f"{SOURCE_MAP_NAME}: {exc}")
        return tuple(errors)

    try:
        surface = prepared_review_surface(paper_dir.name)
    except (OSError, RuntimeError, TypeError, ValueError) as exc:
        missing_stages = packet_lean_cache_missing_stages(paper_dir, source_map)
        if missing_stages:
            errors.append(
                f"{PACKET_LEAN_CACHE_NAME}: stale or incomplete for the current saved "
                "Lean review graph (missing " + ", ".join(missing_stages) + ")"
            )
        else:
            errors.append(
                f"docs/{PACKET_NAME}.tex: cannot validate current packet rendering: {exc}"
            )
        return tuple(errors)
    if surface.presentation_authority not in {"accepted_graph", "current_v11_graph"}:
        missing_stages = packet_lean_cache_missing_stages(paper_dir, source_map)
        if missing_stages:
            errors.append(
                f"{PACKET_LEAN_CACHE_NAME}: stale or incomplete for the current saved "
                "Lean review graph (missing " + ", ".join(missing_stages) + ")"
            )
            return tuple(errors)

    tex_path = paper_dir / "docs" / f"{PACKET_NAME}.tex"
    if not tex_path.is_file():
        return tuple(errors)
    try:
        expected = _packet_tex_currentness_text(render_packet(
            surface,
            template=PACKET_TEMPLATE_PATH.read_text(encoding="utf-8"),
            generated_date=dt.date.today().isoformat(),
        ))
        actual = _packet_tex_currentness_text(
            tex_path.read_text(encoding="utf-8")
        )
    except (OSError, RuntimeError, ValueError) as exc:
        errors.append(
            f"docs/{PACKET_NAME}.tex: cannot validate current packet rendering: {exc}"
        )
    else:
        if actual != expected:
            errors.append(
                f"docs/{PACKET_NAME}.tex: stale relative to the current saved Lean "
                "review graph and semantic ledgers"
            )
    return tuple(errors)
