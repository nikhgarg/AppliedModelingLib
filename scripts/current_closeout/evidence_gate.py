"""Accept the complete current evidence conjunction for one exact transaction.

The large evidence validator still owns the substantive source, fidelity,
independence, metadata, and build-route checks shared with historical
diagnostics.  This module owns the *current accepting transaction*: it requires
the exact builder-issued v11 context and its already-accepted primary gate,
runs every current evidence family against frozen inputs, and is the only
production caller allowed to issue the nominal evidence capability.

Keeping validation and acceptance distinct lets shared validators move into
smaller semantic owners without creating a second accepting lane or weakening
the conjunction during that refactor.
"""

from __future__ import annotations

from collections.abc import MutableMapping
from pathlib import Path
from typing import Any

from scripts.current_closeout.evidence_acceptance import (
    _issue_current_v11_evidence_integrity,
)
from scripts.current_closeout.primary_gate_transaction import (
    accepted_current_v11_primary_gate,
)
from scripts.evidence_run_context import V11EvidenceRunContext

CURRENT_EVIDENCE_TRANSACTION_FAMILIES = (
    "duplicate_sidecars",
    "placeholder_evidence",
    "assumption_alignment",
    "source_manifest",
    "semantic_contract_inventory",
    "source_route",
    "source_proof_fidelity",
    "validator_independence",
    "human_review_metadata",
    "vacuous_assumptions",
    "active_status",
    "focused_build_route",
)
CURRENT_EVIDENCE_FAMILIES = (
    "report_generator",
    *CURRENT_EVIDENCE_TRANSACTION_FAMILIES,
)


def _current_error(
    validators: Any,
    paper_id: str,
    folder: Path,
    message: str,
) -> object:
    finding = validators.Finding
    rel = validators.rel
    return finding("ERROR", paper_id, rel(folder / "status.json"), message)


def current_evidence_transaction_findings(
    *,
    folder: Path,
    context: V11EvidenceRunContext,
    release: bool,
    require_source_bytes: bool,
    active: set[str],
    defaults: set[str],
    libraries: set[str],
) -> list[object]:
    """Evaluate the named current evidence families without issuing authority.

    Standalone diagnostics and the accepting gate share this exact conjunction.
    Only :func:`run_current_evidence_gate` may turn the resulting list into a
    transaction-bound capability.
    """

    from scripts import audit_evidence_integrity as validators
    from scripts import source_manifest_validation as source_validation

    status = context.status
    status_payload = context.status_payload
    review_log_snapshot = context.json_snapshot(
        folder / ".review_traces" / "paper_theorem_validations.jsonl"
    )
    assumptions_snapshot = context.json_snapshot(folder / "Assumptions.lean")
    families = (
        (
            "duplicate_sidecars",
            lambda: validators.check_duplicate_sidecars(
                folder, status, context=context
            ),
        ),
        (
            "placeholder_evidence",
            lambda: validators.check_placeholder_evidence(
                folder, status, context=context
            ),
        ),
        (
            "assumption_alignment",
            lambda: validators.check_full_closeout_assumption_alignment(
                folder, status, context=context
            ),
        ),
        (
            "source_manifest",
            lambda: validators.check_source_manifest(
                folder,
                status,
                require_source_bytes=require_source_bytes,
                context=context,
            ),
        ),
        (
            "semantic_contract_inventory",
            lambda: validators.semantic_contract_inventory_findings(
                folder,
                status,
                require_source_bytes=require_source_bytes,
                context=context,
            ),
        ),
        (
            "source_route",
            lambda: validators.current_v11_source_route_findings(
                folder,
                status,
                context=context,
            ),
        ),
        (
            "source_proof_fidelity",
            lambda: source_validation.source_proof_fidelity_findings(
                folder,
                status,
                status_payload,
                require_source_bytes=require_source_bytes,
                context=context,
            ),
        ),
        (
            "validator_independence",
            lambda: validators.check_validator_independence(
                folder,
                status,
                release,
                context=context,
            ),
        ),
        (
            "human_review_metadata",
            lambda: validators.check_human_review(
                folder,
                status,
                status_payload,
                release,
                review_log_present=(
                    review_log_snapshot.sha256 is not None
                    if review_log_snapshot is not None
                    else None
                ),
            ),
        ),
        (
            "vacuous_assumptions",
            lambda: validators.check_vacuous_assumptions(
                folder,
                status,
                source_bytes_override=(
                    assumptions_snapshot.raw_bytes
                    if assumptions_snapshot is not None
                    else None
                ),
            ),
        ),
        (
            "active_status",
            lambda: validators.check_active_status(folder, status, active),
        ),
        (
            "focused_build_route",
            lambda: validators.check_build_coverage(
                folder,
                status,
                status_payload,
                defaults,
                libraries,
            ),
        ),
    )
    if (
        tuple(name for name, _evaluate in families)
        != CURRENT_EVIDENCE_TRANSACTION_FAMILIES
    ):
        return [
            _current_error(
                validators,
                folder.name,
                folder,
                "current evidence family registry is incomplete or out of order",
            )
        ]
    findings: list[object] = []
    for _name, evaluate in families:
        findings.extend(evaluate())
    return list(validators.unique_findings(findings))


def run_current_evidence_gate(
    *,
    repository_root: Path,
    paper_id: str,
    release: bool,
    require_source_bytes: bool,
    context: V11EvidenceRunContext,
    diagnostics: MutableMapping[str, int] | None = None,
) -> list[object]:
    """Run and accept every current evidence obligation exactly once.

    The import is intentionally inside the function while shared validation
    families are being separated from the historical CLI/dispatcher.  The
    accepting authority itself has no historical fallback and cannot accept a
    caller-supplied or serialized finding list.
    """

    from scripts import audit_evidence_integrity as validators

    root = repository_root.resolve()
    folder = (root / "papers" / paper_id).resolve()
    if (
        not isinstance(context, V11EvidenceRunContext)
        or not context.issued_by_builder
        or not context.v11_lean_claim_graph_selected
        or context.folder != folder
        or context.status_snapshot.path.resolve() != folder / "status.json"
        or context.audit_config_snapshot.path.resolve()
        != root / "papers" / "audit_config.json"
    ):
        return [
            _current_error(
                validators,
                paper_id,
                folder,
                "current evidence gate requires the exact builder-issued v11 "
                "transaction for the selected paper",
            )
        ]
    if accepted_current_v11_primary_gate(context) is None:
        return [
            _current_error(
                validators,
                paper_id,
                folder,
                "current evidence gate requires the exact in-process primary "
                "acceptance before evidence validation",
            )
        ]

    report_snapshot = context.json_snapshot(
        root / "scripts" / "refresh_validation_report_audit_summaries.py"
    )
    lake_snapshot = context.json_snapshot(root / "lakefile.toml")
    if (
        report_snapshot is None
        or not isinstance(report_snapshot.raw_bytes, bytes)
        or lake_snapshot is None
        or not isinstance(lake_snapshot.raw_bytes, bytes)
    ):
        return [
            _current_error(
                validators,
                paper_id,
                folder,
                "current evidence transaction did not freeze the repository "
                "report generator and lakefile inputs",
            )
        ]

    defaults, libraries = validators.lake_targets(
        raw_bytes_override=lake_snapshot.raw_bytes,
    )
    active = validators.active_papers_from_payload(
        context.audit_config_snapshot.payload or {}
    )
    findings = list(
        validators.check_report_generator(
            raw_bytes_override=report_snapshot.raw_bytes,
        )
    )
    findings.extend(
        current_evidence_transaction_findings(
            folder=folder,
            context=context,
            release=release,
            require_source_bytes=require_source_bytes,
            active=active,
            defaults=defaults,
            libraries=libraries,
        )
    )
    findings = list(validators.unique_findings(findings))
    if any(getattr(finding, "severity", None) == "ERROR" for finding in findings):
        return list(findings)

    accepted = _issue_current_v11_evidence_integrity(
        context,
        tuple(findings),
        release=release,
        require_source_bytes=require_source_bytes,
    )
    if accepted is None:
        findings.append(
            _current_error(
                validators,
                paper_id,
                folder,
                "current evidence conjunction passed but its exact "
                "transaction-bound capability could not be issued",
            )
        )
    return list(findings)


__all__ = [
    "CURRENT_EVIDENCE_FAMILIES",
    "CURRENT_EVIDENCE_TRANSACTION_FAMILIES",
    "current_evidence_transaction_findings",
    "run_current_evidence_gate",
]
