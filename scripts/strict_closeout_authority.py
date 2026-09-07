#!/usr/bin/env python3
"""Authenticate current runtime authority and historical stage authorities.

Current closeout authority comes only from the in-process runtime capability
and contains no operational stage hashes.  The older eight-receipt authority
remains readable for accepted historical graphs, but its stage machinery is
loaded only when that historical schema is actually used.
"""

from __future__ import annotations

import re
from collections.abc import Mapping
from dataclasses import dataclass
from types import MappingProxyType
from typing import TYPE_CHECKING, Any

try:
    from scripts.formalization_engine_identity import normalized_engine_projection
    from scripts.portable_evidence_identity import portable_evidence_sha256
except ModuleNotFoundError:  # Direct ``python scripts/...`` execution.
    from formalization_engine_identity import normalized_engine_projection
    from portable_evidence_identity import portable_evidence_sha256

if TYPE_CHECKING:
    from scripts.closeout_pipeline import CloseoutContext, CloseoutStage, StageReceipt


STRICT_CLOSEOUT_AUTHORITY_SCHEMA = 1
CURRENT_STRICT_CLOSEOUT_AUTHORITY_SCHEMA = 2
CURRENT_STRICT_CLOSEOUT_AUTHORITY_KIND = "current_runtime_pass"
CURRENT_STRICT_CLOSEOUT_CONTRACT_SHA256 = portable_evidence_sha256(
    {
        "schema": 1,
        "contract": (
            "one_in_process_current_closeout_pass_after_primary_evidence_"
            "conclusion_holistic_build_and_final_mutation_gates"
        ),
    }
)
SHA256_RE = re.compile(r"^[0-9a-f]{64}$")


def _legacy_stage_types() -> tuple[object, object, object, object]:
    """Load the retired stage schema only for historical validation."""

    try:
        from scripts.closeout_pipeline import (
            STAGE_DEPENDENCIES,
            CloseoutContext,
            CloseoutStage,
            StageReceipt,
        )
    except ModuleNotFoundError:  # Direct ``python scripts/...`` execution.
        from closeout_pipeline import (  # type: ignore[no-redef]
            STAGE_DEPENDENCIES,
            CloseoutContext,
            CloseoutStage,
            StageReceipt,
        )
    return STAGE_DEPENDENCIES, CloseoutContext, CloseoutStage, StageReceipt


def _legacy_strict_closeout_stages() -> tuple[object, ...]:
    _, _, closeout_stage, _ = _legacy_stage_types()
    return tuple(
        stage
        for stage in closeout_stage
        if stage is not closeout_stage.CANONICAL_RECEIPT
    )


class StrictCloseoutAuthorityError(ValueError):
    """The operational stage chain cannot authorize graph-leaf issuance."""


@dataclass(frozen=True)
class StrictCloseoutAuthority:
    paper: str
    context_sha256: str
    engine_tree_sha256: str
    stage_receipt_sha256s: Mapping[str, str]
    authority_sha256: str

    def projection(self) -> dict[str, Any]:
        return {
            "schema": STRICT_CLOSEOUT_AUTHORITY_SCHEMA,
            "acceptance_credential": False,
            "authority_kind": "authenticated_frozen_strict_closeout",
            "paper": self.paper,
            "context_sha256": self.context_sha256,
            "engine_tree_sha256": self.engine_tree_sha256,
            "stage_receipt_sha256s": dict(self.stage_receipt_sha256s),
            "authority_sha256": self.authority_sha256,
        }


@dataclass(frozen=True)
class CurrentStrictCloseoutAuthority:
    """Portable projection issued only from the runtime current pass.

    Operational stage receipts and context hashes are deliberately absent.
    The accepted graph separately binds the exact semantic graph, paper index,
    holistic surface, source assurance, and engine.  This value records which
    current closeout contract authorized their publication without turning
    recovery telemetry into semantic identity.
    """

    paper: str
    engine_tree_sha256: str
    closeout_contract_sha256: str
    authority_sha256: str

    def projection(self) -> dict[str, Any]:
        return {
            "schema": CURRENT_STRICT_CLOSEOUT_AUTHORITY_SCHEMA,
            "acceptance_credential": False,
            "authority_kind": CURRENT_STRICT_CLOSEOUT_AUTHORITY_KIND,
            "paper": self.paper,
            "engine_tree_sha256": self.engine_tree_sha256,
            "closeout_contract_sha256": self.closeout_contract_sha256,
            "authority_sha256": self.authority_sha256,
        }


def validate_strict_closeout_authority(
    authority: object,
) -> StrictCloseoutAuthority | CurrentStrictCloseoutAuthority:
    """Fail closed if a typed authority was mutated or hand-assembled badly."""

    if isinstance(authority, CurrentStrictCloseoutAuthority):
        if not authority.paper.strip():
            raise StrictCloseoutAuthorityError("strict closeout paper is empty")
        for field, value in (
            ("engine tree", authority.engine_tree_sha256),
            ("closeout contract", authority.closeout_contract_sha256),
            ("authority", authority.authority_sha256),
        ):
            if not SHA256_RE.fullmatch(value):
                raise StrictCloseoutAuthorityError(
                    f"strict closeout {field} is not SHA-256"
                )
        material = {
            "schema": CURRENT_STRICT_CLOSEOUT_AUTHORITY_SCHEMA,
            "acceptance_credential": False,
            "authority_kind": CURRENT_STRICT_CLOSEOUT_AUTHORITY_KIND,
            "paper": authority.paper,
            "engine_tree_sha256": authority.engine_tree_sha256,
            "closeout_contract_sha256": authority.closeout_contract_sha256,
        }
        if portable_evidence_sha256(material) != authority.authority_sha256:
            raise StrictCloseoutAuthorityError(
                "strict closeout authority identity is corrupt"
            )
        return authority
    if not isinstance(authority, StrictCloseoutAuthority):
        raise StrictCloseoutAuthorityError(
            "strict closeout authority is not the nominal authenticated object"
        )
    if not authority.paper.strip():
        raise StrictCloseoutAuthorityError("strict closeout paper is empty")
    for field, value in (
        ("context", authority.context_sha256),
        ("engine tree", authority.engine_tree_sha256),
        ("authority", authority.authority_sha256),
    ):
        if not SHA256_RE.fullmatch(value):
            raise StrictCloseoutAuthorityError(
                f"strict closeout {field} is not SHA-256"
            )
    expected_stage_names = {
        stage.value for stage in _legacy_strict_closeout_stages()
    }
    if set(authority.stage_receipt_sha256s) != expected_stage_names:
        raise StrictCloseoutAuthorityError(
            "strict closeout authority does not name exactly all operational stages"
        )
    if any(
        not SHA256_RE.fullmatch(value)
        for value in authority.stage_receipt_sha256s.values()
    ):
        raise StrictCloseoutAuthorityError(
            "strict closeout authority contains a malformed stage identity"
        )
    material = {
        "schema": STRICT_CLOSEOUT_AUTHORITY_SCHEMA,
        "acceptance_credential": False,
        "authority_kind": "authenticated_frozen_strict_closeout",
        "paper": authority.paper,
        "context_sha256": authority.context_sha256,
        "engine_tree_sha256": authority.engine_tree_sha256,
        "stage_receipt_sha256s": dict(authority.stage_receipt_sha256s),
    }
    if portable_evidence_sha256(material) != authority.authority_sha256:
        raise StrictCloseoutAuthorityError(
            "strict closeout authority identity is corrupt"
        )
    return authority


def recorded_strict_closeout_authority(
    value: object,
) -> StrictCloseoutAuthority | CurrentStrictCloseoutAuthority:
    """Validate the portable projection retained by an accepted graph.

    Only the live strict executor may mint the nominal object originally passed
    to publication.  After Git transport, the accepted graph retains this exact
    projection so another machine can authenticate its historical issuance
    without ignored stage files or a machine-local checkout path.
    """

    if not isinstance(value, Mapping):
        raise StrictCloseoutAuthorityError(
            "recorded strict closeout authority is not an object"
        )
    schema = value.get("schema")
    if schema == CURRENT_STRICT_CLOSEOUT_AUTHORITY_SCHEMA:
        required = {
            "schema",
            "acceptance_credential",
            "authority_kind",
            "paper",
            "engine_tree_sha256",
            "closeout_contract_sha256",
            "authority_sha256",
        }
        if (
            set(value) != required
            or value.get("acceptance_credential") is not False
            or value.get("authority_kind") != CURRENT_STRICT_CLOSEOUT_AUTHORITY_KIND
        ):
            raise StrictCloseoutAuthorityError(
                "recorded current strict closeout authority fields are malformed"
            )
        return validate_strict_closeout_authority(
            CurrentStrictCloseoutAuthority(
                paper=str(value.get("paper") or ""),
                engine_tree_sha256=str(value.get("engine_tree_sha256") or ""),
                closeout_contract_sha256=str(
                    value.get("closeout_contract_sha256") or ""
                ),
                authority_sha256=str(value.get("authority_sha256") or ""),
            )
        )
    required = {
        "schema",
        "acceptance_credential",
        "authority_kind",
        "paper",
        "context_sha256",
        "engine_tree_sha256",
        "stage_receipt_sha256s",
        "authority_sha256",
    }
    raw_stages = value.get("stage_receipt_sha256s")
    if (
        set(value) != required
        or value.get("schema") != STRICT_CLOSEOUT_AUTHORITY_SCHEMA
        or value.get("acceptance_credential") is not False
        or value.get("authority_kind")
        != "authenticated_frozen_strict_closeout"
        or not isinstance(raw_stages, Mapping)
    ):
        raise StrictCloseoutAuthorityError(
            "recorded strict closeout authority fields are malformed"
        )
    authority = StrictCloseoutAuthority(
        paper=str(value.get("paper") or ""),
        context_sha256=str(value.get("context_sha256") or ""),
        engine_tree_sha256=str(value.get("engine_tree_sha256") or ""),
        stage_receipt_sha256s=MappingProxyType(
            {str(key): str(digest) for key, digest in raw_stages.items()}
        ),
        authority_sha256=str(value.get("authority_sha256") or ""),
    )
    return validate_strict_closeout_authority(authority)


def issue_current_strict_closeout_authority(
    current_pass: object,
) -> CurrentStrictCloseoutAuthority:
    """Issue the portable current authority from the exact runtime pass."""

    from scripts.current_closeout.pass_capability import (
        validate_current_closeout_pass,
    )

    accepted = validate_current_closeout_pass(current_pass)
    engine, error = normalized_engine_projection(accepted.engine_registration())
    if engine is None:
        raise StrictCloseoutAuthorityError(
            "current strict closeout pass has invalid engine registration: " + error
        )
    material = {
        "schema": CURRENT_STRICT_CLOSEOUT_AUTHORITY_SCHEMA,
        "acceptance_credential": False,
        "authority_kind": CURRENT_STRICT_CLOSEOUT_AUTHORITY_KIND,
        "paper": accepted.paper,
        "engine_tree_sha256": engine["engine_tree_sha256"],
        "closeout_contract_sha256": CURRENT_STRICT_CLOSEOUT_CONTRACT_SHA256,
    }
    return validate_strict_closeout_authority(
        CurrentStrictCloseoutAuthority(
            paper=accepted.paper,
            engine_tree_sha256=str(engine["engine_tree_sha256"]),
            closeout_contract_sha256=CURRENT_STRICT_CLOSEOUT_CONTRACT_SHA256,
            authority_sha256=portable_evidence_sha256(material),
        )
    )


def authenticate_strict_closeout_authority(
    context: CloseoutContext,
    stages: Mapping[CloseoutStage, StageReceipt],
    engine_registration: Mapping[str, object],
) -> StrictCloseoutAuthority:
    """Bind all eight validated stage receipts to one portable leaf authority."""

    stage_dependencies, closeout_context, _, stage_receipt = _legacy_stage_types()
    strict_closeout_stages = _legacy_strict_closeout_stages()
    if not isinstance(context, closeout_context):
        raise StrictCloseoutAuthorityError(
            "strict closeout authority requires the nominal frozen context"
        )
    engine, engine_error = normalized_engine_projection(engine_registration)
    if engine is None:
        raise StrictCloseoutAuthorityError(
            "strict closeout authority has invalid engine registration: "
            + engine_error
        )
    missing = [
        stage.value for stage in strict_closeout_stages if stage not in stages
    ]
    if missing:
        raise StrictCloseoutAuthorityError(
            "strict closeout authority is missing stages: " + ", ".join(missing)
        )

    receipt_sha256s: dict[str, str] = {}
    for stage in strict_closeout_stages:
        receipt = stages[stage]
        if not isinstance(receipt, stage_receipt):
            raise StrictCloseoutAuthorityError(
                f"strict closeout stage {stage.value} is not a validated receipt"
            )
        if (
            receipt.stage is not stage
            or receipt.paper != context.paper
            or receipt.context_sha256 != context.context_sha256
        ):
            raise StrictCloseoutAuthorityError(
                f"strict closeout stage {stage.value} belongs to another context"
            )
        expected_dependencies = {
            dependency.value: stages[dependency].receipt_sha256
            for dependency in stage_dependencies[stage]
        }
        if dict(receipt.dependency_receipt_sha256s) != expected_dependencies:
            raise StrictCloseoutAuthorityError(
                f"strict closeout stage {stage.value} has a broken dependency chain"
            )
        receipt_sha256s[stage.value] = receipt.receipt_sha256

    material = {
        "schema": STRICT_CLOSEOUT_AUTHORITY_SCHEMA,
        "acceptance_credential": False,
        "authority_kind": "authenticated_frozen_strict_closeout",
        "paper": context.paper,
        "context_sha256": context.context_sha256,
        "engine_tree_sha256": engine["engine_tree_sha256"],
        "stage_receipt_sha256s": receipt_sha256s,
    }
    return validate_strict_closeout_authority(StrictCloseoutAuthority(
        paper=context.paper,
        context_sha256=context.context_sha256,
        engine_tree_sha256=str(engine["engine_tree_sha256"]),
        stage_receipt_sha256s=MappingProxyType(receipt_sha256s),
        authority_sha256=portable_evidence_sha256(material),
    ))
