"""Small nominal capability for the current evidence-integrity verdict.

The evidence validator owns computation.  This module owns only the
transaction-bound acceptance object so terminal publication can recognize the
verdict without importing the 20k-line validator or any historical lane.
"""

from __future__ import annotations

from scripts.evidence_run_context import (
    EvidenceRunContextIssuerBinding,
    V11EvidenceRunContext,
)

_EVIDENCE_ACCEPTANCE_ISSUER = object()


class AcceptedCurrentV11EvidenceIntegrity:
    """Nominal proof of one exact accepted current evidence verdict."""

    __slots__ = (
        "context",
        "findings",
        "primary",
        "release",
        "require_source_bytes",
    )

    def __init__(
        self,
        issuer: object,
        *,
        context: V11EvidenceRunContext,
        primary: object,
        findings: tuple[object, ...],
        release: bool,
        require_source_bytes: bool,
    ) -> None:
        if issuer is not _EVIDENCE_ACCEPTANCE_ISSUER:
            raise TypeError(
                "current v11 evidence acceptance is issued only by its gate"
            )
        self.context = context
        self.primary = primary
        self.findings = findings
        self.release = release
        self.require_source_bytes = require_source_bytes


def _issue_current_v11_evidence_integrity(
    context: V11EvidenceRunContext,
    findings: tuple[object, ...],
    *,
    release: bool,
    require_source_bytes: bool,
) -> AcceptedCurrentV11EvidenceIntegrity | None:
    """Bind an error-free evidence verdict to the exact primary capability."""

    if not isinstance(context, V11EvidenceRunContext) or not context.issued_by_builder:
        return None
    binding = context._issuer_token
    if not isinstance(binding, EvidenceRunContextIssuerBinding):
        return None
    primary = binding.current_v11_primary_gate_acceptance
    primary_result = getattr(primary, "result", None)
    if (
        primary is None
        or getattr(primary, "context", None) is not context
        or getattr(primary_result, "accepted", False) is not True
        or any(getattr(finding, "severity", None) == "ERROR" for finding in findings)
    ):
        return None
    existing = binding.current_v11_evidence_integrity_acceptance
    if (
        isinstance(existing, AcceptedCurrentV11EvidenceIntegrity)
        and existing.context is context
        and existing.primary is primary
        and existing.findings is findings
        and existing.release is release
        and existing.require_source_bytes is require_source_bytes
    ):
        return existing
    accepted = AcceptedCurrentV11EvidenceIntegrity(
        _EVIDENCE_ACCEPTANCE_ISSUER,
        context=context,
        primary=primary,
        findings=findings,
        release=release,
        require_source_bytes=require_source_bytes,
    )
    binding.current_v11_evidence_integrity_acceptance = accepted
    return accepted


def accepted_current_v11_evidence_integrity(
    context: object,
) -> AcceptedCurrentV11EvidenceIntegrity | None:
    """Return only the exact gate-issued current evidence acceptance."""

    if not isinstance(context, V11EvidenceRunContext) or not context.issued_by_builder:
        return None
    binding = context._issuer_token
    if not isinstance(binding, EvidenceRunContextIssuerBinding):
        return None
    accepted = binding.current_v11_evidence_integrity_acceptance
    primary = binding.current_v11_primary_gate_acceptance
    if not (
        isinstance(accepted, AcceptedCurrentV11EvidenceIntegrity)
        and accepted.context is context
        and primary is not None
        and accepted.primary is primary
        and getattr(primary, "context", None) is context
        and getattr(getattr(primary, "result", None), "accepted", False) is True
        and not any(
            getattr(finding, "severity", None) == "ERROR"
            for finding in accepted.findings
        )
    ):
        return None
    return accepted


def has_current_v11_evidence_integrity_acceptance(context: object) -> bool:
    """Whether ``context`` owns the exact accepted evidence verdict."""

    return accepted_current_v11_evidence_integrity(context) is not None


__all__ = [
    "AcceptedCurrentV11EvidenceIntegrity",
    "accepted_current_v11_evidence_integrity",
    "has_current_v11_evidence_integrity_acceptance",
]
