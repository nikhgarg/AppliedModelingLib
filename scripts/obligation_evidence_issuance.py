#!/usr/bin/env python3
"""Portable issuance attestations for immutable obligation-evidence leaves.

A leaf says *what semantic fact was established*. An issuance attestation says
*which accepted transaction and validated record were authorized to mint that
fact*. Keeping these objects separate prevents prompt wording, reviewer labels,
producer implementations, and report layout from invalidating an unchanged
mathematical result while retaining exact forensic provenance.

An issuance attestation is not independently a paper-closeout credential. A
terminal verifier must authenticate the named authority, validate the current
leaf graph and current source/Lean controls, and only then grant acceptance.
"""

from __future__ import annotations

import re
from dataclasses import dataclass
from typing import Any, Mapping

try:
    from scripts.portable_evidence_identity import portable_evidence_sha256
except ModuleNotFoundError:  # Direct ``python scripts/...`` execution.
    from portable_evidence_identity import portable_evidence_sha256


OBLIGATION_EVIDENCE_ISSUANCE_SCHEMA = 1
SHA256_RE = re.compile(r"^[0-9a-f]{64}$")
LEGACY_ACCEPTED_TRANSACTION_ASSURANCE_SHA256 = portable_evidence_sha256(
    {
        "schema": 1,
        "contract": (
            "mechanical_projection_of_record_authenticated_by_existing_strict_"
            "accepted_closeout_transaction"
        ),
    }
)
STRICT_CLOSEOUT_TRANSACTION_ASSURANCE_SHA256 = portable_evidence_sha256(
    {
        "schema": 1,
        "contract": (
            "mechanical_projection_of_exact_record_authenticated_by_the_complete_"
            "frozen_strict_closeout_stage_transaction"
        ),
    }
)
EXACT_SEMANTIC_REBIND_ASSURANCE_SHA256 = portable_evidence_sha256(
    {
        "schema": 1,
        "contract": (
            "accepted_raw_source_semantic_judgment_rebound_to_independently_"
            "reproduced_exact_source_display_declaration_and_lean_leaf"
        ),
    }
)
TERMINAL_PAPER_CLOSURE_ASSURANCE_SHA256 = portable_evidence_sha256(
    {
        "schema": 1,
        "contract": (
            "registered_terminal_verifier_rechecked_the_complete_current_"
            "paper_obligation_graph_and_all_current_source_lean_and_build_controls"
        ),
    }
)


class ObligationEvidenceIssuanceError(ValueError):
    """An issuance attestation is malformed or content-corrupt."""


def _sha256(value: object, field: str) -> str:
    text = str(value or "").strip().lower()
    if not SHA256_RE.fullmatch(text):
        raise ObligationEvidenceIssuanceError(
            f"{field} is not a lowercase SHA-256 digest"
        )
    return text


@dataclass(frozen=True)
class ObligationEvidenceIssuance:
    """One immutable provenance edge from an authority to a semantic leaf."""

    leaf_sha256: str
    assurance_contract_sha256: str
    authority_sha256: str
    evidence_record_sha256: str
    issuance_sha256: str

    def projection(self) -> dict[str, Any]:
        return {
            "schema": OBLIGATION_EVIDENCE_ISSUANCE_SCHEMA,
            "acceptance_credential": False,
            "leaf_sha256": self.leaf_sha256,
            "assurance_contract_sha256": self.assurance_contract_sha256,
            "authority_sha256": self.authority_sha256,
            "evidence_record_sha256": self.evidence_record_sha256,
            "issuance_sha256": self.issuance_sha256,
        }


def issue_obligation_evidence_attestation(
    *,
    leaf_sha256: str,
    assurance_contract_sha256: str,
    authority_sha256: str,
    evidence_record_sha256: str,
) -> ObligationEvidenceIssuance:
    material = {
        "schema": OBLIGATION_EVIDENCE_ISSUANCE_SCHEMA,
        "acceptance_credential": False,
        "leaf_sha256": _sha256(leaf_sha256, "issued leaf"),
        "assurance_contract_sha256": _sha256(
            assurance_contract_sha256, "assurance contract"
        ),
        "authority_sha256": _sha256(authority_sha256, "issuing authority"),
        "evidence_record_sha256": _sha256(
            evidence_record_sha256, "evidence record"
        ),
    }
    issuance = ObligationEvidenceIssuance(
        leaf_sha256=material["leaf_sha256"],
        assurance_contract_sha256=material["assurance_contract_sha256"],
        authority_sha256=material["authority_sha256"],
        evidence_record_sha256=material["evidence_record_sha256"],
        issuance_sha256=portable_evidence_sha256(material),
    )
    return validate_obligation_evidence_issuance(issuance.projection())


def validate_obligation_evidence_issuance(
    value: object,
) -> ObligationEvidenceIssuance:
    if not isinstance(value, Mapping):
        raise ObligationEvidenceIssuanceError("issuance is not an object")
    required = {
        "schema",
        "acceptance_credential",
        "leaf_sha256",
        "assurance_contract_sha256",
        "authority_sha256",
        "evidence_record_sha256",
        "issuance_sha256",
    }
    if set(value) != required:
        raise ObligationEvidenceIssuanceError("issuance fields are malformed")
    if (
        value.get("schema") != OBLIGATION_EVIDENCE_ISSUANCE_SCHEMA
        or value.get("acceptance_credential") is not False
    ):
        raise ObligationEvidenceIssuanceError("issuance schema is unsupported")
    material = {
        "schema": OBLIGATION_EVIDENCE_ISSUANCE_SCHEMA,
        "acceptance_credential": False,
        "leaf_sha256": _sha256(value.get("leaf_sha256"), "issued leaf"),
        "assurance_contract_sha256": _sha256(
            value.get("assurance_contract_sha256"), "assurance contract"
        ),
        "authority_sha256": _sha256(
            value.get("authority_sha256"), "issuing authority"
        ),
        "evidence_record_sha256": _sha256(
            value.get("evidence_record_sha256"), "evidence record"
        ),
    }
    supplied = _sha256(value.get("issuance_sha256"), "issuance identity")
    expected = portable_evidence_sha256(material)
    if supplied != expected:
        raise ObligationEvidenceIssuanceError("issuance identity is corrupt")
    return ObligationEvidenceIssuance(
        leaf_sha256=material["leaf_sha256"],
        assurance_contract_sha256=material["assurance_contract_sha256"],
        authority_sha256=material["authority_sha256"],
        evidence_record_sha256=material["evidence_record_sha256"],
        issuance_sha256=supplied,
    )
