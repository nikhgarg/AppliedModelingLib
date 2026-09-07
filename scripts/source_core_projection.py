"""Validate optional literal-source-core map projections.

This small, dependency-free module is shared by the historical diagnostic and
the current closeout preflight. It validates explicit map associations only:
it neither parses Lean nor infers a source claim from a declaration name.
"""

from collections.abc import Mapping

SOURCE_CORE_PROJECTION_CLASSIFICATION = "literal_source_core"
CHECKED_STRENGTHENING_CLASSIFICATION = (
    "checked_strengthening_not_literal_source_coverage"
)


def _nonempty_qualified_declaration(value: object) -> str | None:
    if not isinstance(value, str):
        return None
    declaration = value.strip()
    parts = declaration.split(".")
    if len(parts) < 2 or any(not part for part in parts):
        return None
    return declaration


def _nonempty_string(value: object) -> str | None:
    if not isinstance(value, str):
        return None
    return value.strip() or None


def _string_list_or_none(value: object) -> list[str] | None:
    if not isinstance(value, list):
        return None
    values = [_nonempty_string(entry) for entry in value]
    if any(entry is None for entry in values):
        return None
    return [entry for entry in values if entry is not None]


def _declaration_reference_matches(reference: str, declaration: str) -> bool:
    """Accept a map's exact qualified declaration or its legacy short form."""

    return reference in {declaration, declaration.rsplit(".", maxsplit=1)[-1]}


def validation_errors(raw_item: object) -> list[str]:
    """Validate one optional source-core/checked-strengthening projection."""

    if not isinstance(raw_item, Mapping):
        return []
    raw_projection = raw_item.get("source_core_projection")
    if raw_projection is None:
        return []
    if not isinstance(raw_projection, Mapping):
        return ["source_core_projection must be an object"]

    errors: list[str] = []
    if raw_projection.get("classification") != SOURCE_CORE_PROJECTION_CLASSIFICATION:
        errors.append(
            "source_core_projection.classification must be "
            f"`{SOURCE_CORE_PROJECTION_CLASSIFICATION}`"
        )
    if _nonempty_string(raw_projection.get("description")) is None:
        errors.append("source_core_projection.description must be a nonempty string")

    core_direct = _nonempty_qualified_declaration(
        raw_projection.get("direct_declaration")
    )
    if core_direct is None:
        errors.append(
            "source_core_projection.direct_declaration must be a nonempty fully-qualified declaration"
        )
    core_spec = _nonempty_qualified_declaration(raw_projection.get("spec_declaration"))
    if core_spec is None:
        errors.append(
            "source_core_projection.spec_declaration must be a nonempty fully-qualified declaration"
        )

    raw_contract = raw_item.get("semantic_contract")
    if not isinstance(raw_contract, Mapping):
        errors.append(
            "source_core_projection requires an item semantic_contract object for exact direct/spec binding"
        )
    else:
        contract_direct = _nonempty_string(raw_contract.get("evidence_declaration"))
        contract_spec = _nonempty_string(raw_contract.get("spec_declaration"))
        if core_direct is not None and core_direct != contract_direct:
            errors.append(
                "source_core_projection.direct_declaration must equal "
                "semantic_contract.evidence_declaration"
            )
        if core_spec is not None and core_spec != contract_spec:
            errors.append(
                "source_core_projection.spec_declaration must equal "
                "semantic_contract.spec_declaration"
            )

    primary_declarations = _string_list_or_none(raw_item.get("lean_declarations"))
    if core_direct is not None:
        if primary_declarations is None or len(primary_declarations) != 1 or not (
            _declaration_reference_matches(primary_declarations[0], core_direct)
        ):
            errors.append(
                "source_core_projection direct declaration must be the sole "
                "lean_declarations entry (qualified or legacy short form)"
            )
    elif primary_declarations is None:
        errors.append("lean_declarations must be a list of nonempty strings")

    support_declarations = _string_list_or_none(
        raw_item.get("support_lean_declarations")
    )
    if support_declarations is None:
        errors.append("support_lean_declarations must be a list of nonempty strings")
        support_declarations = []
    if primary_declarations is None:
        primary_declarations = []

    raw_strengthenings = raw_item.get("checked_strengthening_declarations")
    # A direct source route need not have a separate strengthening.  When one
    # exists it must be explicit and independently classified; requiring an
    # artificial strengthening would turn a literal source claim into a
    # bookkeeping failure.
    if raw_strengthenings is None:
        raw_strengthenings = []
    elif not isinstance(raw_strengthenings, list) or not raw_strengthenings:
        errors.append(
            "checked_strengthening_declarations must be a nonempty list of objects"
        )
        return errors

    core_identities = {identity for identity in (core_direct, core_spec) if identity}
    for index, raw_strengthening in enumerate(raw_strengthenings):
        prefix = f"checked_strengthening_declarations[{index}]"
        if not isinstance(raw_strengthening, Mapping):
            errors.append(f"{prefix} must be an object")
            continue
        if (
            raw_strengthening.get("classification")
            != CHECKED_STRENGTHENING_CLASSIFICATION
        ):
            errors.append(
                f"{prefix}.classification must be "
                f"`{CHECKED_STRENGTHENING_CLASSIFICATION}`"
            )
        strengthening_declaration = _nonempty_qualified_declaration(
            raw_strengthening.get("declaration")
        )
        if strengthening_declaration is None:
            errors.append(
                f"{prefix}.declaration must be a nonempty fully-qualified declaration"
            )
        strengthening_spec = _nonempty_qualified_declaration(
            raw_strengthening.get("spec_declaration")
        )
        if strengthening_spec is None:
            errors.append(
                f"{prefix}.spec_declaration must be a nonempty fully-qualified declaration"
            )
        if _nonempty_string(raw_strengthening.get("description")) is None:
            errors.append(f"{prefix}.description must be a nonempty string")
        if strengthening_declaration in core_identities:
            errors.append(
                f"{prefix}.declaration must differ from both source-core direct/spec declarations"
            )
        if strengthening_spec in core_identities:
            errors.append(
                f"{prefix}.spec_declaration must differ from both source-core direct/spec declarations"
            )
        if strengthening_declaration is None:
            continue
        if not any(
            _declaration_reference_matches(reference, strengthening_declaration)
            for reference in support_declarations
        ):
            errors.append(
                f"{prefix}.declaration must occur in support_lean_declarations "
                "(qualified or legacy short form)"
            )
        if any(
            _declaration_reference_matches(reference, strengthening_declaration)
            for reference in primary_declarations
        ):
            errors.append(
                f"{prefix}.declaration must not occur in lean_declarations"
            )
    return errors
