#!/usr/bin/env python3
"""Portable semantic identity for source-proof-fidelity review ledgers.

The closeout engine may regenerate container metadata freely, but a paper's
accepted semantic surface must continue to bind the source claim, reviewed
proof scope, repair obligation, resolution, evidence, and status impact of
every recorded defect.  This module is intentionally independent of the large
legacy evidence auditor so terminal credential checks can reuse the same
projection without importing or rerunning that auditor.
"""

from __future__ import annotations

import copy
from collections.abc import Mapping

try:
    from scripts.portable_evidence_identity import portable_evidence_sha256
except ModuleNotFoundError:  # Direct ``python scripts/...`` execution.
    from portable_evidence_identity import portable_evidence_sha256


def source_proof_fidelity_semantic_projection(value: object) -> object | None:
    """Project the substantive content of one schema-2 fidelity ledger.

    ``defect_kind`` and the historical spelling of proof-scope ``outcome`` are
    controlled routing/container labels.  All mathematical and disposition
    fields remain exact.  An absent optional collection is equivalent to the
    producer's stored ``null``.
    """

    if (
        not isinstance(value, Mapping)
        or isinstance(value.get("schema"), bool)
        or value.get("schema") != 2
    ):
        return None
    defects = value.get("defects")
    if not isinstance(defects, list) or any(
        not isinstance(defect, Mapping) for defect in defects
    ):
        return None
    projection = copy.deepcopy(dict(value))
    projected_defects = projection.get("defects")
    if not isinstance(projected_defects, list):  # pragma: no cover - deepcopy.
        return None
    for defect in projected_defects:
        if not isinstance(defect, dict):  # pragma: no cover - checked above.
            return None
        defect.pop("defect_kind", None)
    outcome_classes = {
        "clarifications_recorded": "no_defect",
        "no_endpoint_defect": "no_defect",
        "no_defect": "no_defect",
        "proof_defect_repaired_same_endpoint": "defect_recorded",
        "proof_defects_repaired_same_endpoint": "defect_recorded",
        "defect_recorded": "defect_recorded",
    }
    projected_scopes = projection.get("reviewed_proof_scopes")
    if isinstance(projected_scopes, list):
        for scope in projected_scopes:
            if not isinstance(scope, dict):
                return None
            outcome = str(scope.get("outcome") or "").strip()
            if outcome not in outcome_classes:
                return None
            scope["outcome"] = outcome_classes[outcome]
    for optional_collection in ("model_conventions", "checked_proof_steps"):
        if projection.get(optional_collection) is None:
            projection.pop(optional_collection, None)
    return projection


def source_proof_fidelity_semantic_sha256(value: object) -> str:
    """Return the portable substantive identity, or ``""`` if malformed."""

    projection = source_proof_fidelity_semantic_projection(value)
    return portable_evidence_sha256(projection) if projection is not None else ""


__all__ = [
    "source_proof_fidelity_semantic_projection",
    "source_proof_fidelity_semantic_sha256",
]
