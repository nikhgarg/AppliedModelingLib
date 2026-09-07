"""Runtime-only authority for one complete current closeout transaction.

Operational traces, stage receipts, process exit codes, and serialized Python
objects are intentionally insufficient to construct this capability.  The
current executor issues it only after every strict gate and the final mutation
check have run in one exact ``V11EvidenceRunContext``.  Publication consumes
that same object in the same process.
"""

from __future__ import annotations

import json
import re
from collections.abc import Mapping, Sequence
from pathlib import Path
from typing import Any

from scripts.closeout_plan_receipt import (
    resolved_plan_final_holistic_audit_surface,
    resolved_plan_lean_closure_projection,
    resolved_plan_v11_lean_review_graph,
)
from scripts.current_closeout.evidence_acceptance import (
    accepted_current_v11_evidence_integrity,
)
from scripts.current_closeout.strict_transaction import (
    STRICT_CLOSEOUT_EXECUTION_STAGES,
)
from scripts.evidence_run_context import (
    EvidenceRunContextIssuerBinding,
    V11EvidenceRunContext,
)
from scripts.final_holistic_audit_surface import (
    final_holistic_audit_surface_sha256,
)
from scripts.formalization_engine_identity import (
    current_registered_engine_projection,
    normalized_engine_projection,
)

_CURRENT_CLOSEOUT_PASS_ISSUER = object()
_SHA256_RE = re.compile(r"^[0-9a-f]{64}$")


def _accepted_primary(context: object) -> object | None:
    from scripts.current_closeout.primary_gate_transaction import (
        accepted_current_v11_primary_gate,
    )

    return accepted_current_v11_primary_gate(context)


def _accepted_evidence(context: object) -> object | None:
    return accepted_current_v11_evidence_integrity(context)


class CurrentCloseoutPassError(ValueError):
    """The current executor did not establish one exact terminal pass."""


def _canonical_json_bytes(value: Mapping[str, object]) -> bytes:
    return json.dumps(
        value,
        ensure_ascii=True,
        sort_keys=True,
        separators=(",", ":"),
    ).encode("utf-8")


class CurrentCloseoutPass:
    """Issuer-protected, nonserializable proof of one current strict run."""

    __slots__ = (
        "_build_input_provider",
        "_engine_bytes",
        "_evidence_acceptance",
        "_evidence_context",
        "_final_holistic_surface_bytes",
        "_lean_closure_bytes",
        "_lean_review_graph_bytes",
        "_lean_review_graph_sha256",
        "_paper",
        "_plan_identity",
        "_plan_receipt_bytes",
        "_primary_acceptance",
        "_repository_root",
        "_sealed",
    )

    def __init__(
        self,
        issuer: object,
        *,
        repository_root: Path,
        paper: str,
        plan_identity: str,
        plan_receipt: Mapping[str, object],
        evidence_context: V11EvidenceRunContext,
        primary_acceptance: object,
        evidence_acceptance: object,
        engine_registration: Mapping[str, object],
        lean_closure_projection: Mapping[str, object],
        lean_review_graph: Mapping[str, object],
        lean_review_graph_sha256: str,
        final_holistic_surface: Mapping[str, object],
        build_input_provider: object,
    ) -> None:
        if issuer is not _CURRENT_CLOSEOUT_PASS_ISSUER:
            raise TypeError(
                "current closeout passes are issued only by the strict executor"
            )
        object.__setattr__(self, "_sealed", False)
        object.__setattr__(self, "_repository_root", repository_root.resolve())
        object.__setattr__(self, "_paper", paper)
        object.__setattr__(self, "_plan_identity", plan_identity)
        object.__setattr__(self, "_plan_receipt_bytes", _canonical_json_bytes(plan_receipt))
        object.__setattr__(self, "_evidence_context", evidence_context)
        object.__setattr__(self, "_primary_acceptance", primary_acceptance)
        object.__setattr__(self, "_evidence_acceptance", evidence_acceptance)
        object.__setattr__(self, "_engine_bytes", _canonical_json_bytes(engine_registration))
        object.__setattr__(self, "_lean_closure_bytes", _canonical_json_bytes(lean_closure_projection))
        object.__setattr__(self, "_lean_review_graph_bytes", _canonical_json_bytes(lean_review_graph))
        object.__setattr__(self, "_lean_review_graph_sha256", lean_review_graph_sha256)
        object.__setattr__(self, "_final_holistic_surface_bytes", _canonical_json_bytes(final_holistic_surface))
        object.__setattr__(self, "_build_input_provider", build_input_provider)
        object.__setattr__(self, "_sealed", True)

    def __setattr__(self, name: str, value: object) -> None:
        if getattr(self, "_sealed", False):
            raise TypeError("current closeout pass is immutable")
        object.__setattr__(self, name, value)

    def __copy__(self) -> CurrentCloseoutPass:
        raise TypeError("current closeout pass cannot be copied")

    def __deepcopy__(self, memo: object) -> CurrentCloseoutPass:
        del memo
        raise TypeError("current closeout pass cannot be copied")

    def __reduce__(self) -> object:
        raise TypeError("current closeout pass cannot be serialized")

    @property
    def repository_root(self) -> Path:
        return self._repository_root

    @property
    def paper(self) -> str:
        return self._paper

    @property
    def plan_identity(self) -> str:
        return self._plan_identity

    @property
    def evidence_context(self) -> V11EvidenceRunContext:
        return self._evidence_context

    @property
    def primary_acceptance(self) -> object:
        return self._primary_acceptance

    @property
    def evidence_acceptance(self) -> object:
        return self._evidence_acceptance

    @property
    def build_input_provider(self) -> object:
        return self._build_input_provider

    @property
    def lean_review_graph_sha256(self) -> str:
        return self._lean_review_graph_sha256

    def plan_receipt(self) -> dict[str, Any]:
        return json.loads(self._plan_receipt_bytes)

    def engine_registration(self) -> dict[str, Any]:
        return json.loads(self._engine_bytes)

    def lean_closure_projection(self) -> dict[str, Any]:
        return json.loads(self._lean_closure_bytes)

    def lean_review_graph(self) -> dict[str, Any]:
        return json.loads(self._lean_review_graph_bytes)

    def final_holistic_surface(self) -> dict[str, Any]:
        return json.loads(self._final_holistic_surface_bytes)


def _issue_current_closeout_pass(
    repository_root: Path,
    paper: str,
    *,
    plan_identity: str,
    plan_receipt: Mapping[str, object],
    evidence_context: object,
    completed_stages: Sequence[str],
    findings: Sequence[object],
) -> CurrentCloseoutPass:
    """Issue the one terminal capability from the current executor only."""

    root = repository_root.resolve()
    folder = (root / "papers" / paper).resolve()
    if (
        not isinstance(evidence_context, V11EvidenceRunContext)
        or not evidence_context.issued_by_builder
        or evidence_context.folder != folder
        or tuple(completed_stages) != STRICT_CLOSEOUT_EXECUTION_STAGES
        or not _SHA256_RE.fullmatch(plan_identity)
        or plan_receipt.get("paper") != paper
        or plan_receipt.get("plan_identity_sha256") != plan_identity
        or any(getattr(finding, "severity", None) == "ERROR" for finding in findings)
    ):
        raise CurrentCloseoutPassError(
            "current closeout pass requires one complete error-free issued transaction"
        )
    binding = evidence_context._issuer_token
    if not isinstance(binding, EvidenceRunContextIssuerBinding) or binding.context is not evidence_context:
        raise CurrentCloseoutPassError(
            "current closeout pass has no exact evidence-context issuer"
        )
    primary = _accepted_primary(evidence_context)
    evidence = _accepted_evidence(evidence_context)
    if (
        primary is None
        or evidence is None
        or getattr(evidence, "primary", None) is not primary
    ):
        raise CurrentCloseoutPassError(
            "current closeout pass requires exact primary and evidence verdicts"
        )
    existing = accepted_current_closeout_pass(evidence_context)
    if existing is not None:
        return existing
    engine, engine_error = current_registered_engine_projection(root)
    if engine is None:
        raise CurrentCloseoutPassError(
            engine_error or "registered current engine is unavailable"
        )
    normalized_engine, normalized_error = normalized_engine_projection(engine)
    if normalized_engine is None:
        raise CurrentCloseoutPassError(normalized_error)
    try:
        lean_closure = resolved_plan_lean_closure_projection(root, plan_receipt)
        lean_graph = resolved_plan_v11_lean_review_graph(root, plan_receipt)
        final_surface = resolved_plan_final_holistic_audit_surface(root, plan_receipt)
    except (OSError, RuntimeError, TypeError, ValueError) as exc:
        raise CurrentCloseoutPassError(
            f"current closeout plan projections are unavailable: {exc}"
        ) from exc
    if not isinstance(lean_closure, Mapping):
        raise CurrentCloseoutPassError("current closeout has no Lean closure projection")
    if not isinstance(lean_graph, Mapping):
        raise CurrentCloseoutPassError("current closeout has no v11 Lean review graph")
    if not isinstance(final_surface, Mapping):
        raise CurrentCloseoutPassError("current closeout has no final holistic surface")
    expected_final_sha = str(
        plan_receipt.get("final_holistic_audit_surface_sha256") or ""
    )
    if final_holistic_audit_surface_sha256(final_surface) != expected_final_sha:
        raise CurrentCloseoutPassError(
            "current closeout final holistic surface is not plan-bound"
        )
    raw_graph_reference = plan_receipt.get("v11_lean_review_graph")
    graph_sha = (
        str(raw_graph_reference.get("sha256") or "")
        if isinstance(raw_graph_reference, Mapping)
        else ""
    )
    if not _SHA256_RE.fullmatch(graph_sha):
        raise CurrentCloseoutPassError(
            "current closeout v11 Lean graph identity is unavailable"
        )
    primary_surface = getattr(primary, "surface", None)
    build_input_provider = getattr(primary_surface, "build_input_provider", None)
    if build_input_provider is None:
        raise CurrentCloseoutPassError(
            "current closeout pass has no primary-owned Lean build-input provider"
        )
    accepted = CurrentCloseoutPass(
        _CURRENT_CLOSEOUT_PASS_ISSUER,
        repository_root=root,
        paper=paper,
        plan_identity=plan_identity,
        plan_receipt=plan_receipt,
        evidence_context=evidence_context,
        primary_acceptance=primary,
        evidence_acceptance=evidence,
        engine_registration=normalized_engine,
        lean_closure_projection=lean_closure,
        lean_review_graph=lean_graph,
        lean_review_graph_sha256=graph_sha,
        final_holistic_surface=final_surface,
        build_input_provider=build_input_provider,
    )
    binding.current_closeout_pass = accepted
    return accepted


def accepted_current_closeout_pass(context: object) -> CurrentCloseoutPass | None:
    """Recognize only the exact pass retained by its issued v11 context."""

    if not isinstance(context, V11EvidenceRunContext) or not context.issued_by_builder:
        return None
    binding = context._issuer_token
    if not isinstance(binding, EvidenceRunContextIssuerBinding):
        return None
    accepted = binding.current_closeout_pass
    if not isinstance(accepted, CurrentCloseoutPass):
        return None
    if (
        accepted.evidence_context is not context
        or accepted.primary_acceptance is not _accepted_primary(context)
        or accepted.evidence_acceptance is not _accepted_evidence(context)
        or accepted.build_input_provider
        is not getattr(accepted.primary_acceptance.surface, "build_input_provider", None)
        or accepted.repository_root / "papers" / accepted.paper != context.folder
    ):
        return None
    return accepted


def validate_current_closeout_pass(value: object) -> CurrentCloseoutPass:
    """Reject copied, foreign, stale, or non-issued publication authority."""

    if not isinstance(value, CurrentCloseoutPass):
        raise CurrentCloseoutPassError(
            "accepted-graph publication requires the current in-process pass"
        )
    if accepted_current_closeout_pass(value.evidence_context) is not value:
        raise CurrentCloseoutPassError(
            "current closeout pass is not bound to its exact evidence transaction"
        )
    return value


def bind_current_closeout_pass_authority(
    current_pass: object,
    authority: object,
) -> None:
    """Bind one portable issuance projection to the exact runtime pass."""

    accepted = validate_current_closeout_pass(current_pass)
    binding = accepted.evidence_context._issuer_token
    assert isinstance(binding, EvidenceRunContextIssuerBinding)
    existing = binding.current_closeout_pass_authority
    if existing is not None and existing is not authority:
        raise CurrentCloseoutPassError(
            "current closeout pass cannot bind multiple portable authorities"
        )
    binding.current_closeout_pass_authority = authority


def current_closeout_pass_authority(current_pass: object) -> object:
    """Return the exact portable authority derived from this runtime pass."""

    accepted = validate_current_closeout_pass(current_pass)
    binding = accepted.evidence_context._issuer_token
    assert isinstance(binding, EvidenceRunContextIssuerBinding)
    authority = binding.current_closeout_pass_authority
    if authority is None:
        raise CurrentCloseoutPassError(
            "current closeout pass has not issued its portable authority"
        )
    return authority


__all__ = [
    "CurrentCloseoutPass",
    "CurrentCloseoutPassError",
    "accepted_current_closeout_pass",
    "bind_current_closeout_pass_authority",
    "current_closeout_pass_authority",
    "validate_current_closeout_pass",
]
