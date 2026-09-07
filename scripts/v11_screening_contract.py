#!/usr/bin/env python3
"""Pure container contract for v11 source-to-Spec screening ledgers."""

from __future__ import annotations

from dataclasses import dataclass
from typing import Mapping


V11_SCREENING_SCHEMA = 3
V11_SCREENING_PROMPT_VERSION = (
    "statement-match-v11-verbatim-source-anchor-lean-expanded-spec-"
    "claim-atoms-supporting-declarations-v4"
)


@dataclass(frozen=True)
class V11ScreeningContainerValidation:
    """Cheap structural verdict that grants no semantic acceptance."""

    errors: tuple[str, ...]
    usable_item_ledger: bool

    @property
    def current(self) -> bool:
        return not self.errors


def validate_v11_screening_container(
    payload: object,
    *,
    paper: str,
) -> V11ScreeningContainerValidation:
    """Validate identity and mandatory container fields without reading Lean."""

    if not isinstance(payload, Mapping):
        return V11ScreeningContainerValidation(
            errors=(
                "missing or malformed v11 raw-source-to-expanded-Spec screening",
            ),
            usable_item_ledger=False,
        )

    errors: list[str] = []
    identity_current = (
        payload.get("schema") == V11_SCREENING_SCHEMA
        and payload.get("paper") == paper
    )
    if not identity_current:
        errors.append("v11 screening has an unsupported schema or paper identity")
    if str(payload.get("prompt_version") or "").strip() != (
        V11_SCREENING_PROMPT_VERSION
    ):
        errors.append(
            "v11 screening does not declare the required raw-source prompt version"
        )
    if not str(payload.get("validator") or "").strip() or not str(
        payload.get("validated_at") or ""
    ).strip():
        errors.append("v11 screening lacks reviewer and validation-time metadata")
    item_ledger_present = isinstance(payload.get("items"), Mapping)
    if not item_ledger_present:
        errors.append("v11 screening has no item ledger")
    return V11ScreeningContainerValidation(
        errors=tuple(errors),
        usable_item_ledger=identity_current and item_ledger_present,
    )
