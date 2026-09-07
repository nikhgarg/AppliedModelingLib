#!/usr/bin/env python3
"""Shared exact-source atom schema used by closeout producers and consumers."""

from __future__ import annotations

import hashlib
import json
import re
from typing import Any, Mapping

try:
    from scripts.portable_evidence_identity import portable_evidence_sha256
except ModuleNotFoundError:  # Direct ``python scripts/...`` execution.
    from portable_evidence_identity import portable_evidence_sha256


SHA256_RE = re.compile(r"^[0-9a-f]{64}$")
IDENTITY_SCHEMA_FIELD = "identity_schema"
SOURCE_QUOTE_SHA256_FIELD = "source_quote_sha256"
VERBATIM_CLAUSE_FIELD = "verbatim_source_clause"
LEGACY_IDENTITY_SCHEMA = 1
EXACT_QUOTE_IDENTITY_SCHEMA = 2
EXACT_CLAUSE_IDENTITY_SCHEMA = 3
EXACT_IDENTITY_SCHEMAS = frozenset(
    {EXACT_QUOTE_IDENTITY_SCHEMA, EXACT_CLAUSE_IDENTITY_SCHEMA}
)
SUPPORTED_IDENTITY_SCHEMAS = frozenset(
    {LEGACY_IDENTITY_SCHEMA, *EXACT_IDENTITY_SCHEMAS}
)
SOURCE_CLAIM_ATOMS_SCHEMA = 1
SOURCE_CLAIM_ATOM_REQUIRED_FIELDS = frozenset(
    {"id", "source_locator", "semantic_claim", "reviewed_lean_route"}
)
SOURCE_CLAIM_ATOM_FIELDS = frozenset(
    set(SOURCE_CLAIM_ATOM_REQUIRED_FIELDS)
    | {
        SOURCE_QUOTE_SHA256_FIELD,
        VERBATIM_CLAUSE_FIELD,
        IDENTITY_SCHEMA_FIELD,
    }
)
SOURCE_CLAIM_ATOM_ID_RE = re.compile(r"^[A-Za-z0-9][A-Za-z0-9_.:-]*$")
SOURCE_FILE_LINE_RE = re.compile(
    r"(?P<path>[A-Za-z0-9_./-]+\.(?:tex|txt|md|pdf)):"
    r"(?P<start>\d+)(?:-(?P<end>\d+))?",
    re.I,
)
PLACEHOLDER_SOURCE_RE = re.compile(
    r"\b(?:tbd|todo|not recorded|not available)\b|"
    r"^\s*unknown(?:\s+(?:source )?(?:claim|statement|semantics)\b|[\s.!]*$)|"
    r"exact source location (?:to be )?refined|"
    r"paper-facing review target|"
    r"paper source location recorded by group-level|"
    r"source location recorded by group-level|"
    r"exact premise is the Lean audit-premise key",
    re.I,
)
SOURCE_SPEC_CORRESPONDENCE_FIELDS = frozenset(
    {
        "schema",
        "source_atoms_sha256",
        "spec_closure_sha256",
        "spec_surface_sha256",
        "closure_environment_sha256",
        "item_identity_sha256",
        "source_atom_bindings",
        "closure_node_dispositions",
    }
)


def _canonical_json_payload(payload: Any) -> Any:
    if isinstance(payload, dict):
        return {
            key: _canonical_json_payload(value)
            for key, value in sorted(payload.items())
        }
    if isinstance(payload, list):
        return sorted(
            (_canonical_json_payload(value) for value in payload),
            key=lambda value: json.dumps(
                value, sort_keys=True, separators=(",", ":")
            ),
        )
    return payload


def _canonical_json_digest(payload: Any) -> str:
    encoded = json.dumps(
        _canonical_json_payload(payload),
        sort_keys=True,
        separators=(",", ":"),
    ).encode("utf-8")
    return hashlib.sha256(encoded).hexdigest()


def graph_native_source_spec_realization_identity_sha256(
    raw_contract: object,
    *,
    source_atoms_sha256: str,
    spec_closure_sha256: str,
    spec_surface_sha256: str,
    closure_environment_sha256: str,
) -> str:
    """Bind one runtime v11 source/Spec receipt to its exact graph material.

    The current v11 graph already authenticates the transparent Spec, its exact
    proof endpoint, recursive semantic prerequisites, and axiom closure.  Once
    the exact source-to-expanded-Spec screening has passed, a second persisted
    atom-to-closure worksheet adds no mathematical authority.  This portable
    identity lets the same immutable transaction mint the narrow runtime
    capability consumed by occurrence/conclusion checks.

    The function deliberately accepts only content digests plus the typed
    semantic contract.  Paper ids, checkout paths, declaration line numbers,
    and engine-version pairs are not semantic identity.
    """

    digests = (
        source_atoms_sha256,
        spec_closure_sha256,
        spec_surface_sha256,
        closure_environment_sha256,
    )
    if not isinstance(raw_contract, Mapping) or any(
        not isinstance(value, str) or not SHA256_RE.fullmatch(value.strip())
        for value in digests
    ):
        return ""
    return portable_evidence_sha256(
        {
            "schema": 1,
            "authority": "v11_graph_native_realization",
            "semantic_contract": dict(raw_contract),
            "source_atoms_sha256": source_atoms_sha256.strip().lower(),
            "spec_closure_sha256": spec_closure_sha256.strip().lower(),
            "spec_surface_sha256": spec_surface_sha256.strip().lower(),
            "closure_environment_sha256": (
                closure_environment_sha256.strip().lower()
            ),
        }
    )


def _meaningful_semantic_text(value: object) -> bool:
    if not isinstance(value, str):
        return False
    text = value.strip()
    return len(text) >= 8 and not PLACEHOLDER_SOURCE_RE.search(text)


def source_claim_atoms_validation_errors(
    raw_atoms: object,
    *,
    require_source_quote: bool = False,
) -> list[str]:
    """Validate the portable source-first theorem-clause atom schema."""

    if not isinstance(raw_atoms, list) or not raw_atoms:
        return ["source_claim_atoms must be a nonempty list"]

    errors: list[str] = []
    seen_ids: set[str] = set()
    schemas: set[int] = set()
    for index, raw_atom in enumerate(raw_atoms):
        prefix = f"source_claim_atoms[{index}]"
        if not isinstance(raw_atom, dict):
            errors.append(f"{prefix} must be an object")
            continue
        unexpected = sorted(set(raw_atom) - SOURCE_CLAIM_ATOM_FIELDS)
        if unexpected:
            errors.append(
                f"{prefix} has unsupported field(s): " + ", ".join(unexpected)
            )
        missing = sorted(SOURCE_CLAIM_ATOM_REQUIRED_FIELDS - set(raw_atom))
        if missing:
            errors.append(
                f"{prefix} is missing required field(s): " + ", ".join(missing)
            )

        atom_id = raw_atom.get("id")
        if not isinstance(atom_id, str) or not SOURCE_CLAIM_ATOM_ID_RE.fullmatch(
            atom_id.strip()
        ):
            errors.append(f"{prefix}.id must use a nonempty stable atom identifier")
        elif atom_id.strip() in seen_ids:
            errors.append(f"{prefix}.id duplicates `{atom_id.strip()}`")
        else:
            seen_ids.add(atom_id.strip())

        locator = raw_atom.get("source_locator")
        matches = (
            list(SOURCE_FILE_LINE_RE.finditer(locator))
            if isinstance(locator, str)
            else []
        )
        if not isinstance(locator, str) or not locator.strip():
            errors.append(f"{prefix}.source_locator must be a nonempty string")
        elif len(matches) != 1:
            errors.append(
                f"{prefix}.source_locator must contain exactly one file:line source span"
            )

        semantic_claim = raw_atom.get("semantic_claim")
        if not _meaningful_semantic_text(semantic_claim):
            errors.append(
                f"{prefix}.semantic_claim must contain a substantive source-facing claim"
            )

        route = raw_atom.get("reviewed_lean_route")
        if not isinstance(route, str) or not route.strip():
            errors.append(f"{prefix}.reviewed_lean_route must be a nonempty string")
        elif isinstance(semantic_claim, str) and semantic_claim.strip() in {
            route.strip(),
            route.strip().rsplit(".", 1)[-1],
        }:
            errors.append(
                f"{prefix}.semantic_claim cannot be a Lean route/name in place of source semantics"
            )

        quote_digest = raw_atom.get(SOURCE_QUOTE_SHA256_FIELD)
        raw_schema = raw_atom.get(IDENTITY_SCHEMA_FIELD, LEGACY_IDENTITY_SCHEMA)
        schema = identity_schema(raw_atom)
        if schema is None:
            errors.append(
                f"{prefix}.{IDENTITY_SCHEMA_FIELD} must be one of: "
                + ", ".join(str(value) for value in sorted(SUPPORTED_IDENTITY_SCHEMAS))
            )
        else:
            schemas.add(schema)
        if quote_digest is None and (
            require_source_quote or raw_schema in EXACT_IDENTITY_SCHEMAS
        ):
            errors.append(
                f"{prefix}.{SOURCE_QUOTE_SHA256_FIELD} is required for exact-quote atom identity or source-spec correspondence"
            )
        elif quote_digest is not None and (
            not isinstance(quote_digest, str)
            or not SHA256_RE.fullmatch(quote_digest.strip())
        ):
            errors.append(
                f"{prefix}.{SOURCE_QUOTE_SHA256_FIELD} must be a SHA-256 digest when present"
            )
        verbatim_clause = raw_atom.get(VERBATIM_CLAUSE_FIELD)
        if raw_schema == EXACT_CLAUSE_IDENTITY_SCHEMA:
            if not isinstance(verbatim_clause, str) or not verbatim_clause.strip():
                errors.append(
                    f"{prefix}.{VERBATIM_CLAUSE_FIELD} is required for exact-clause atom identity"
                )
        elif verbatim_clause is not None:
            errors.append(
                f"{prefix}.{VERBATIM_CLAUSE_FIELD} requires "
                f"{IDENTITY_SCHEMA_FIELD} {EXACT_CLAUSE_IDENTITY_SCHEMA}"
            )
    if len(schemas) > 1:
        errors.append("source_claim_atoms in one source item must use one identity schema")
    return errors


def source_claim_atom_semantic_sha256(raw_atom: object) -> str:
    """Return one name-free, source-first atom identity."""

    if not isinstance(raw_atom, dict):
        return ""
    schema = identity_schema(raw_atom)
    if schema is None:
        return ""
    quote_digest = raw_atom.get(SOURCE_QUOTE_SHA256_FIELD)
    if schema in EXACT_IDENTITY_SCHEMAS:
        if not isinstance(quote_digest, str) or not SHA256_RE.fullmatch(
            quote_digest.strip()
        ):
            return ""
        identity: dict[str, object] = {
            "schema": schema,
            SOURCE_QUOTE_SHA256_FIELD: quote_digest.strip().lower(),
            "component_protocol": "one_exact_verbatim_quote",
        }
        if schema == EXACT_CLAUSE_IDENTITY_SCHEMA:
            clause = raw_atom.get(VERBATIM_CLAUSE_FIELD)
            if not isinstance(clause, str) or not clause.strip():
                return ""
            identity["component_protocol"] = "one_exact_verbatim_clause_within_quote"
            identity["source_clause_sha256"] = hashlib.sha256(
                clause.encode("utf-8")
            ).hexdigest()
        return _canonical_json_digest(identity)

    locator = raw_atom.get("source_locator")
    claim = raw_atom.get("semantic_claim")
    if not isinstance(locator, str) or not locator.strip():
        return ""
    if not _meaningful_semantic_text(claim):
        return ""
    identity = {
        "source_locator": locator.strip(),
        "semantic_claim": str(claim).strip(),
    }
    if quote_digest is not None:
        if not isinstance(quote_digest, str) or not SHA256_RE.fullmatch(
            quote_digest.strip()
        ):
            return ""
        identity[SOURCE_QUOTE_SHA256_FIELD] = quote_digest.strip().lower()
    return _canonical_json_digest(identity)


def source_claim_atoms_semantic_sha256(raw_atoms: object) -> str:
    """Hash one complete, unambiguous source-claim atom inventory."""

    if source_claim_atoms_validation_errors(raw_atoms):
        return ""
    assert isinstance(raw_atoms, list)
    atoms = [source_claim_atom_semantic_sha256(atom) for atom in raw_atoms]
    if not atoms or any(not SHA256_RE.fullmatch(atom) for atom in atoms):
        return ""
    if len(set(atoms)) != len(atoms):
        return ""
    schema = identity_schema(raw_atoms[0])
    aggregate: dict[str, object] = {
        "schema": SOURCE_CLAIM_ATOMS_SCHEMA,
        "source_atoms": sorted(atoms),
    }
    if schema in EXACT_IDENTITY_SCHEMAS:
        aggregate[IDENTITY_SCHEMA_FIELD] = schema
    return _canonical_json_digest(aggregate)


def _source_spec_correspondence_identity_payload(
    raw_contract: object,
    raw_correspondence: object,
) -> dict[str, Any] | None:
    if not isinstance(raw_contract, dict) or not isinstance(raw_correspondence, dict):
        return None
    required = SOURCE_SPEC_CORRESPONDENCE_FIELDS - {"item_identity_sha256"}
    if not required.issubset(raw_correspondence):
        return None
    return {
        "schema": raw_correspondence.get("schema"),
        "source_atoms_sha256": raw_correspondence.get("source_atoms_sha256"),
        "spec_closure_sha256": raw_correspondence.get("spec_closure_sha256"),
        "spec_surface_sha256": raw_correspondence.get("spec_surface_sha256"),
        "closure_environment_sha256": raw_correspondence.get(
            "closure_environment_sha256"
        ),
        "source_atom_bindings": raw_correspondence.get("source_atom_bindings"),
        "closure_node_dispositions": raw_correspondence.get(
            "closure_node_dispositions"
        ),
        "evidence_mode": raw_contract.get("evidence_mode"),
        "semantic_shape": raw_contract.get("semantic_shape"),
    }


def source_spec_correspondence_item_identity_sha256(
    raw_contract: object,
    raw_correspondence: object,
) -> str:
    """Return the exact structural reuse identity for one realization record."""

    payload = _source_spec_correspondence_identity_payload(
        raw_contract, raw_correspondence
    )
    return _canonical_json_digest(payload) if payload is not None else ""


def identity_schema(raw_atom: Mapping[str, Any]) -> int | None:
    """Return one supported non-Boolean schema number, or ``None``."""

    raw = raw_atom.get(IDENTITY_SCHEMA_FIELD, LEGACY_IDENTITY_SCHEMA)
    if (
        not isinstance(raw, int)
        or isinstance(raw, bool)
        or raw not in SUPPORTED_IDENTITY_SCHEMAS
    ):
        return None
    return raw


def obligation_source_component_sha256(raw_atom: Mapping[str, Any]) -> str:
    """Project one atom onto the source-component identity used by the graph.

    Schemas 1 and 2 preserve the existing whole-quote component identity.
    Schema 3 adds the exact verbatim-clause digest, allowing independently
    stated clauses inside one byte-pinned theorem environment to remain
    distinct without using curator prose, atom ids, or Lean names.
    """

    schema = identity_schema(raw_atom)
    quote = str(raw_atom.get(SOURCE_QUOTE_SHA256_FIELD) or "").strip().lower()
    if schema is None or not SHA256_RE.fullmatch(quote):
        return ""
    component: dict[str, object] = {
        "schema": 1,
        SOURCE_QUOTE_SHA256_FIELD: quote,
        "component_protocol": "one_exact_verbatim_quote",
    }
    if schema == EXACT_CLAUSE_IDENTITY_SCHEMA:
        clause = raw_atom.get(VERBATIM_CLAUSE_FIELD)
        if not isinstance(clause, str) or not clause.strip():
            return ""
        component["component_protocol"] = (
            "one_exact_verbatim_clause_within_quote"
        )
        component["source_clause_sha256"] = hashlib.sha256(
            clause.encode("utf-8")
        ).hexdigest()
    elif VERBATIM_CLAUSE_FIELD in raw_atom:
        return ""
    return portable_evidence_sha256(component)
