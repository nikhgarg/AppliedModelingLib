#!/usr/bin/env python3
"""Regression tests for semantic source-record target dispositions."""

from __future__ import annotations

import importlib.util
import json
import sys
import tempfile
import unittest
from copy import deepcopy
from pathlib import Path
from unittest.mock import patch

ROOT = Path(__file__).resolve().parents[2]
for import_root in (ROOT, ROOT / "scripts"):
    import_root_text = str(import_root)
    if import_root_text not in sys.path:
        sys.path.insert(0, import_root_text)

from scripts import audit_evidence_integrity as EVIDENCE  # noqa: E402
from scripts import audit_repository as REPOSITORY  # noqa: E402
from scripts import source_record_target_disposition as DISPOSITION  # noqa: E402
from scripts import source_record_target_disposition as CANONICAL_DISPOSITION  # noqa: E402
from scripts.source_record_integrity import (  # noqa: E402
    stamp_source_record_audit_receipts,
)

SOURCE_AUDIT_PATH = (
    ROOT / "skills" / "econcs-formalizer" / "scripts" / "source_record_audit.py"
)

SOURCE_AUDIT_SPEC = importlib.util.spec_from_file_location(
    "source_record_audit_target_disposition_fixture", SOURCE_AUDIT_PATH
)
assert SOURCE_AUDIT_SPEC is not None and SOURCE_AUDIT_SPEC.loader is not None
SOURCE_AUDIT = importlib.util.module_from_spec(SOURCE_AUDIT_SPEC)
sys.modules[SOURCE_AUDIT_SPEC.name] = SOURCE_AUDIT
SOURCE_AUDIT_SPEC.loader.exec_module(SOURCE_AUDIT)

from scripts import audit_conclusion_provenance as CONCLUSION  # noqa: E402
PROMPT_VERSION = "source-record-v10-semantic-conclusion-boundary-contract"
SOURCE_KEY = "opaque_source_identity"
SEMANTIC_KEY = "semantic-model::opaque_surface"
DIMENSION = "carrier_and_domain"
DEFECT_ID = "SOURCE-DEFECT-42"
CONVENTION_ID = "MODEL-CONVENTION-9"


def complete_v10_scan_fixture(payload: dict[str, object], *, has_surface: bool) -> None:
    """Populate mandatory generated scan evidence for a synthetic v10 audit."""

    source_file = "papers/Fixture/PaperInterface.lean"
    source_sha256 = "c" * 64
    payload.setdefault("missing_configured_review_rows", [])
    payload.setdefault("recursion_failures", [])
    payload.setdefault("recursion_failure_count", 0)
    payload.setdefault("constructor_result_type_check_error", "")
    payload.setdefault("source_premise_consistency_schema", 1)
    payload.setdefault("source_premise_consistency_error", "")
    payload.setdefault("source_premise_consistency_items", [])
    payload.setdefault("source_premise_consistency_item_count", 0)
    payload.setdefault("review_row_count", 1 if has_surface else 0)
    payload.setdefault("configured_review_rows", [{}] if has_surface else [])
    payload.setdefault("configured_review_rows_count", 1 if has_surface else 0)
    payload.setdefault("configured_review_row_count", 1 if has_surface else 0)
    payload.setdefault("recursive_field_count", 0)
    payload.setdefault(
        "review_interface_source", {"path": source_file, "sha256": source_sha256}
    )
    if has_surface:
        fresh = {
            "mode": "isolated_temp_overlay",
            "returncode": 0,
            "source_file": source_file,
            "source_sha256": source_sha256,
        }
        payload.setdefault("fresh_source_elaboration", dict(fresh))
        payload.setdefault(
            "lean_check",
            {
                "returncode": 0,
                "requested_checked_rows": [{"row": "fixture", "qualified_declaration": "Fixture.PaperInterface.fixture"}],
                "checked_rows": [{"row": "fixture", "qualified_declaration": "Fixture.PaperInterface.fixture"}],
                "fresh_source_elaboration": dict(fresh),
            },
        )
    else:
        payload.setdefault(
            "fresh_source_elaboration",
            {
                "mode": "not_run_without_lean",
                "source_file": source_file,
                "source_sha256": source_sha256,
            },
        )
        payload.setdefault(
            "lean_check",
            {
                "command": "skipped Lean check: no source-record rows or fields",
                "returncode": 0,
                "requested_checked_rows": [],
                "checked_rows": [],
            },
        )


def corrected_target() -> dict[str, object]:
    target: dict[str, object] = {
        "schema": 1,
        "statement": "The corrected finite-domain target excludes the false archival endpoint.",
        "governing_defect_ids": [DEFECT_ID],
        "archival_equivalence_claimed": False,
    }
    target["corrected_target_sha256"] = DISPOSITION.corrected_target_record_digest(
        target
    )
    return target


def statement_map(
    *, corrected: bool, source_key: str = SOURCE_KEY
) -> dict[str, object]:
    item: dict[str, object] = {
        "source_location": "source.tex:4-8",
        "coverage_status": "covered",
    }
    if corrected:
        item.update(
            {
                "coverage_status": "corrected_source_statement",
                "source_defect_ids": [DEFECT_ID],
                "corrected_target": corrected_target(),
            }
        )
    return {"items": {source_key: item}}


def reviewed_signature(*, digest: str = "b" * 64) -> dict[str, str]:
    return {
        "qualified_declaration": "Fixture.Paper.endpoint",
        "elaborated_signature_sha256": digest,
    }


def schema_two_source_identity(
    source_key: str, source_item: dict[str, object]
) -> dict[str, str]:
    return {
        "source_key": source_key,
        "source_location": str(source_item["source_location"]),
        "source_map_item_sha256": DISPOSITION.source_map_item_record_digest(
            source_item
        ),
        "source_semantic_sha256": DISPOSITION.source_item_coverage_sha256(
            source_item, ""
        ),
    }


def schema_two_association(
    source_key: str,
    source_item: dict[str, object],
    *,
    signature: dict[str, str] | None = None,
) -> dict[str, object]:
    signature = signature or reviewed_signature()
    identity = schema_two_source_identity(source_key, source_item)
    association: dict[str, object] = {
        "schema": 2,
        "association_mode": "semantic_contract_group_member",
        "semantic_model_judgment_key": SEMANTIC_KEY,
        "semantic_contract_member_role": "direct_evidence",
        "reviewed_declaration_identity": {
            "qualified_declaration": signature["qualified_declaration"],
            "declaration_sha256": "a" * 64,
        },
        "reviewed_elaborated_signature_identity": signature,
        "source_item_identities": [identity],
        "source_map_item_keys": [source_key],
        "source_map_item_sha256_by_key": {
            source_key: identity["source_map_item_sha256"]
        },
        "source_map_item_keys_sha256": DISPOSITION.source_map_item_record_digest(
            [source_key]
        ),
    }
    association["semantic_association_sha256"] = (
        DISPOSITION.semantic_association_record_digest(
            [identity["source_semantic_sha256"]], signature
        )
    )
    association["association_sha256"] = (
        DISPOSITION.source_contract_association_record_digest(association)
    )
    return association


def schema_two_input_item(
    source_key: str,
    source_item: dict[str, object],
    *,
    signature: dict[str, str] | None = None,
) -> dict[str, object]:
    return {
        "judgment_key": "endpoint.hcondition",
        "source_contract_association": schema_two_association(
            source_key, source_item, signature=signature
        ),
    }


def schema_two_semantic_item(
    source_key: str,
    source_item: dict[str, object],
    *,
    signature: dict[str, str] | None = None,
) -> dict[str, object]:
    signature = signature or reviewed_signature()
    identity = schema_two_source_identity(source_key, source_item)
    association: dict[str, object] = {
        "schema": 2,
        "role": "direct_evidence",
        "reviewed_declaration_identity": {
            "qualified_declaration": signature["qualified_declaration"],
            "declaration_sha256": "a" * 64,
        },
        "reviewed_elaborated_signature_identity": signature,
        "source_item_identities": [identity],
    }
    association["semantic_association_sha256"] = (
        DISPOSITION.semantic_association_record_digest(
            [identity["source_semantic_sha256"]], signature
        )
    )
    return {
        "judgment_key": SEMANTIC_KEY,
        "row": "opaque_surface",
        "qualified_declaration": signature["qualified_declaration"],
        "semantic_contract_source_association": association,
    }


def direct_status_projection_rebind_fixture(
    *, legacy_projection: str = "status_included"
) -> tuple[
    dict[str, object],
    dict[str, object],
    dict[str, object],
    dict[str, object],
    dict[str, object],
    bytes,
    bytes,
]:
    """Build one exact legacy-to-current association transport fixture."""

    source_map = statement_map(corrected=True)
    source_item = source_map["items"][SOURCE_KEY]
    assert isinstance(source_item, dict)
    source_item.update(
        {
            "source_status": "corrected",
            "source_note": "The displayed target has a source correction.",
            "lean_declarations": ["Fixture.Paper.endpoint"],
            # Nested status is deliberately source-semantic and must not be
            # covered by the direct bookkeeping-field exception.
            "source_model": {"source_status": "finite_carrier_only"},
        }
    )
    current_item = schema_two_semantic_item(SOURCE_KEY, source_item)
    current_association = current_item["semantic_contract_source_association"]
    assert isinstance(current_association, dict)
    legacy_association = deepcopy(current_association)
    identities = legacy_association["source_item_identities"]
    assert isinstance(identities, list) and len(identities) == 1
    identity = identities[0]
    assert isinstance(identity, dict)
    if legacy_projection == "status_included":
        identity["source_semantic_sha256"] = (
            DISPOSITION.legacy_source_item_coverage_sha256_before_direct_source_status_exclusion(
                source_item, ""
            )
        )
    elif legacy_projection == "status_excluded":
        identity["source_semantic_sha256"] = (
            DISPOSITION.legacy_source_item_coverage_sha256_schema4_direct_source_status_excluded(
                source_item, ""
            )
        )
    else:  # pragma: no cover - fixture callers must name an explicit transition.
        raise AssertionError(legacy_projection)
    signature = legacy_association["reviewed_elaborated_signature_identity"]
    assert isinstance(signature, dict)
    legacy_association["semantic_association_sha256"] = (
        DISPOSITION.semantic_association_record_digest(
            [identity["source_semantic_sha256"]], signature
        )
    )
    legacy_item = deepcopy(current_item)
    legacy_item["semantic_contract_source_association"] = legacy_association
    raw_audit: dict[str, object] = {
        "paper": "Fixture",
        "source_record_audit_sha256": "e" * 64,
        "semantic_model_items": [legacy_item],
        "boundary_input_items": [],
        "conclusion_dependency_items": [],
        "recursive_field_items": [],
    }
    raw_bytes = json.dumps(raw_audit, sort_keys=True).encode("utf-8")
    map_bytes = json.dumps(source_map, sort_keys=True).encode("utf-8")
    receipt, error = DISPOSITION.build_administrative_projection_rebind(
        paper="Fixture",
        raw_audit=raw_audit,
        raw_audit_bytes=raw_bytes,
        raw_audit_relative_path="audit/source_record_audit.json",
        statement_map=source_map,
        statement_map_bytes=map_bytes,
        statement_map_relative_path="audit/paper_statement_map.json",
    )
    assert error == "" and isinstance(receipt, dict)
    return (
        source_map,
        current_item,
        legacy_item,
        raw_audit,
        receipt,
        raw_bytes,
        map_bytes,
    )


def legacy_direct_statement_map(
    *,
    corrected: bool,
    source_key: str = SOURCE_KEY,
    qualified_declaration: str = "Fixture.Paper.endpoint",
) -> dict[str, object]:
    payload = statement_map(corrected=corrected, source_key=source_key)
    item = payload["items"][source_key]
    assert isinstance(item, dict)
    item.update(
        {
            "title": "Theorem 1: Direct source endpoint",
            "source_kind": "theorem",
            "lean_declarations": [qualified_declaration],
        }
    )
    payload["source_coverage_mode"] = "named_theoretical_statements"
    return payload


def legacy_direct_statement_semantic_item(
    *,
    corrected: bool,
    source_key: str = SOURCE_KEY,
    qualified_declaration: str = "Fixture.Paper.endpoint",
) -> dict[str, object]:
    payload = legacy_direct_statement_map(
        corrected=corrected,
        source_key=source_key,
        qualified_declaration=qualified_declaration,
    )
    source_item = payload["items"][source_key]
    assert isinstance(source_item, dict)
    signature = reviewed_signature()
    signature["qualified_declaration"] = qualified_declaration
    association = SOURCE_AUDIT.explicit_direct_source_route_association(
        source_identities=[
            SOURCE_AUDIT.semantic_contract_source_identity(source_key, source_item)
        ],
        reviewed_identity={
            "qualified_declaration": signature["qualified_declaration"],
            "declaration_sha256": "a" * 64,
        },
        reviewed_signature_identity=signature,
    )
    return {
        "judgment_key": SEMANTIC_KEY,
        "row": "opaque_surface",
        "qualified_declaration": signature["qualified_declaration"],
        "source_statement_association": association,
    }


def fidelity_ledger(*, corrected_resolution: str = "corrected_source_statement") -> dict[str, object]:
    return {
        "defects": [
            {
                "id": DEFECT_ID,
                "statement_impact": "source_statement",
                "resolution": corrected_resolution,
            }
        ],
        "model_conventions": [
            {
                "id": CONVENTION_ID,
                "source_locator": "source.tex:9-12",
                "classification": "explicit_formalization_convention",
                "formal_meaning": "The carrier is explicitly restricted to the finite source domain.",
                "why_needed": "The archival prose leaves the finite carrier boundary implicit.",
                "checked_scope": "The expanded model surface proves the finite carrier translation.",
            }
        ],
    }


def supplemental_scope_ledger(
    *, source_key: object = SOURCE_KEY
) -> dict[str, object]:
    """Add one exact recursive-field source selector to the generic ledger."""

    ledger = fidelity_ledger()
    conventions = ledger["model_conventions"]
    assert isinstance(conventions, list) and len(conventions) == 1
    convention = conventions[0]
    assert isinstance(convention, dict)
    convention["recursive_field_source_scope"] = {
        "schema": 1,
        "entries": [
            {
                "source_item": source_key,
                "root_record": "Fixture.SourceModel",
                "field_chain": [
                    {"structure": "Fixture.SourceModel", "field": "assumption"}
                ],
                "source_locator": "source.tex:4-8",
                "permitted_classifications": ["approved_source_convention"],
            }
        ],
    }
    return ledger


def supplemental_direct_route_fixture(
    *, ordinary_named_presentation: bool = False
) -> tuple[dict[str, object], dict[str, object], dict[str, object]]:
    """Build a direct route whose source item needs a supplemental selector."""

    source_map = legacy_direct_statement_map(corrected=False)
    source_item = source_map["items"][SOURCE_KEY]
    assert isinstance(source_item, dict)
    source_item["claim_bearing"] = False
    if not ordinary_named_presentation:
        source_item["title"] = "Operational model context"
        source_item["source_kind"] = "model"
    signature = reviewed_signature()
    association = SOURCE_AUDIT.explicit_direct_source_route_association(
        source_identities=[
            SOURCE_AUDIT.semantic_contract_source_identity(SOURCE_KEY, source_item)
        ],
        reviewed_identity={
            "qualified_declaration": signature["qualified_declaration"],
            "declaration_sha256": "a" * 64,
        },
        reviewed_signature_identity=signature,
    )
    item = {
        "judgment_key": SEMANTIC_KEY,
        "row": "opaque_surface",
        "qualified_declaration": signature["qualified_declaration"],
        "source_statement_association": association,
    }
    return source_map, item, association


def vocabulary_direct_route_fixture(
) -> tuple[dict[str, object], dict[str, object], dict[str, object]]:
    """Build one generated vocabulary direct-route association.

    Source-domain validation that mints the selector is exercised by the raw
    producer integration test. This fixture intentionally tests the separate
    target-disposition handoff: it consumes the opaque generated selector id,
    but rejects the same association when that receipt is absent.
    """

    source_map = legacy_direct_statement_map(corrected=False)
    source_item = source_map["items"][SOURCE_KEY]
    assert isinstance(source_item, dict)
    source_item.update(
        {
            "title": "Feasible-set vocabulary",
            "source_kind": "predicate_vocabulary",
            "claim_bearing": True,
        }
    )
    signature = reviewed_signature()
    association = SOURCE_AUDIT.explicit_direct_source_route_association(
        source_identities=[
            SOURCE_AUDIT.semantic_contract_source_identity(SOURCE_KEY, source_item)
        ],
        reviewed_identity={
            "qualified_declaration": signature["qualified_declaration"],
            "declaration_sha256": "a" * 64,
        },
        reviewed_signature_identity=signature,
    )
    item = {
        "judgment_key": SEMANTIC_KEY,
        "row": "opaque_surface",
        "qualified_declaration": signature["qualified_declaration"],
        "source_statement_association": association,
    }
    return source_map, item, association


def source_convention_dimension_response(
    association: dict[str, object], ledger: dict[str, object]
) -> dict[str, object]:
    response = schema_two_dimension_response(association)
    response["source_target_disposition"] = "approved_source_convention"
    response["verdict"] = "matches_approved_source_convention"
    response["model_convention_ids"] = [CONVENTION_ID]
    conventions = ledger["model_conventions"]
    assert isinstance(conventions, list) and len(conventions) == 1
    response["model_convention_sha256_by_id"] = {
        CONVENTION_ID: DISPOSITION.model_convention_semantic_digest(conventions[0])
    }
    return response


def semantic_item() -> dict[str, object]:
    return {
        "judgment_key": SEMANTIC_KEY,
        "row": "opaque_surface",
        "source_record_item_digest_schema": 5,
        "source_record_item_semantic_id": "a" * 64,
        "source_record_item_context_sha256": "b" * 64,
        "source_record_item_sha256": "c" * 64,
        "reviewed_elaborated_signature_identities": [
            {
                "qualified_declaration": "Fixture.Paper.endpoint",
                "elaborated_signature_sha256": "d" * 64,
            }
        ],
        "source_record_item_reuse_eligibility": {
            "eligible": True,
            "blockers": [],
        },
        "semantic_contract_source_association": {
            "schema": 1,
            "source_item_identities": [
                {
                    "source_key": SOURCE_KEY,
                    "source_location": "source.tex:4-8",
                }
            ],
        },
        "dimensions": [
            {
                "id": DIMENSION,
                "detected_from_expanded_surface": False,
                "expanded_shape_basis": [],
                "requires_checked_bridge_when_detected": False,
                "requires_parameter_translation_when_detected": False,
            }
        ],
    }


def dimension_response(disposition: str, *, corrected: bool = False) -> dict[str, object]:
    verdicts = {
        "literal_source_match": "matches_literal_source",
        "approved_source_convention": "matches_approved_source_convention",
        "approved_corrected_target": "matches_approved_corrected_target",
    }
    response: dict[str, object] = {
        "verdict": verdicts[disposition],
        "source_locator": "source.tex:4-8",
        "semantic_comparison": "The reviewed finite carrier and target domain are compared from the pinned source formula.",
        "lean_evidence": "The expanded surface exposes the finite carrier restriction directly.",
        "source_target_disposition": disposition,
        "source_map_item_keys": [SOURCE_KEY],
    }
    if disposition == "approved_source_convention":
        response["model_convention_ids"] = [CONVENTION_ID]
        convention = fidelity_ledger()["model_conventions"][0]
        response["model_convention_sha256_by_id"] = {
            CONVENTION_ID: DISPOSITION.model_convention_record_digest(convention)
        }
    if corrected:
        target = corrected_target()
        response["governing_defect_ids"] = [DEFECT_ID]
        response["corrected_target_sha256_by_source_item"] = {
            SOURCE_KEY: target["corrected_target_sha256"]
        }
    return response


def semantic_judgment(response: dict[str, object]) -> dict[str, object]:
    return {
        "classification": "semantic_model_review",
        "prompt_version": PROMPT_VERSION,
        "source_record_audit_sha256": "current-audit-digest",
        "validator": "fixture-reviewer",
        "validated_at": "2026-07-26T00:00:00Z",
        "semantic_model_dimensions": {DIMENSION: response},
    }


def source_contract_input_item(*, corrected: bool) -> dict[str, object]:
    source_item = statement_map(corrected=corrected)["items"][SOURCE_KEY]
    source_digest = DISPOSITION.source_map_item_record_digest(source_item)
    association: dict[str, object] = {
        "schema": 1,
        "association_mode": "semantic_contract_group_member",
        "semantic_model_judgment_key": SEMANTIC_KEY,
        "semantic_contract_member_role": "direct_evidence",
        "reviewed_declaration_identity": {
            "qualified_declaration": "Fixture.Paper.endpoint",
            "declaration_sha256": "a" * 64,
        },
        "source_item_identities": [
            {
                "source_key": SOURCE_KEY,
                "source_location": "source.tex:4-8",
                "source_map_item_sha256": source_digest,
            }
        ],
        "source_map_item_keys": [SOURCE_KEY],
        "source_map_item_sha256_by_key": {SOURCE_KEY: source_digest},
        "source_map_item_keys_sha256": DISPOSITION.source_map_item_record_digest(
            [SOURCE_KEY]
        ),
    }
    association["association_sha256"] = (
        DISPOSITION.source_contract_association_record_digest(association)
    )
    return {
        "judgment_key": "endpoint.hcondition",
        "source_contract_association": association,
    }


def input_response(
    classification: str, *, corrected: bool = False
) -> dict[str, object]:
    item = source_contract_input_item(corrected=corrected)
    association = item["source_contract_association"]
    assert isinstance(association, dict)
    dispositions = {
        "validated_source_assumption": (
            "approved_corrected_target" if corrected else "literal_source_match"
        ),
        "approved_source_convention": "approved_source_convention",
        "approved_corrected_condition": "approved_corrected_target",
    }
    response: dict[str, object] = {
        "classification": classification,
        "source_location": "source.tex:4-8",
        "source_target_disposition": dispositions[classification],
        "source_map_item_keys": [SOURCE_KEY],
        "source_map_item_sha256_by_key": association[
            "source_map_item_sha256_by_key"
        ],
        "source_contract_association_sha256": association["association_sha256"],
    }
    if classification == "approved_source_convention":
        convention = fidelity_ledger()["model_conventions"][0]
        response["model_convention_ids"] = [CONVENTION_ID]
        response["model_convention_sha256_by_id"] = {
            CONVENTION_ID: DISPOSITION.model_convention_record_digest(convention)
        }
    if corrected:
        target = corrected_target()
        response["governing_defect_ids"] = [DEFECT_ID]
        response["corrected_target_sha256_by_source_item"] = {
            SOURCE_KEY: target["corrected_target_sha256"]
        }
    return response


def schema_two_input_response(
    association: dict[str, object], *, corrected: bool = False
) -> dict[str, object]:
    identities = association["source_item_identities"]
    assert isinstance(identities, list) and len(identities) == 1
    identity = identities[0]
    assert isinstance(identity, dict)
    source_key = str(identity["source_key"])
    response: dict[str, object] = {
        "classification": "validated_source_assumption",
        "source_location": str(identity["source_location"]),
        "source_target_disposition": (
            "approved_corrected_target" if corrected else "literal_source_match"
        ),
        # These legacy navigation pins intentionally describe the response's
        # original route. Schema 2 validates the semantic pin below instead.
        "source_map_item_keys": [source_key],
        "source_map_item_sha256_by_key": {
            source_key: identity["source_map_item_sha256"]
        },
        "source_contract_association_sha256": association["association_sha256"],
        "semantic_association_sha256": association[
            "semantic_association_sha256"
        ],
    }
    if corrected:
        target = corrected_target()
        response["governing_defect_ids"] = [DEFECT_ID]
        response["corrected_target_sha256_by_source_semantic_sha256"] = {
            identity["source_semantic_sha256"]: target["corrected_target_sha256"]
        }
    return response


def schema_two_dimension_response(
    association: dict[str, object], *, corrected: bool = False
) -> dict[str, object]:
    identities = association["source_item_identities"]
    assert isinstance(identities, list) and len(identities) == 1
    identity = identities[0]
    assert isinstance(identity, dict)
    disposition = "approved_corrected_target" if corrected else "literal_source_match"
    response: dict[str, object] = {
        "verdict": (
            "matches_approved_corrected_target"
            if corrected
            else "matches_literal_source"
        ),
        "source_locator": str(identity["source_location"]),
        "semantic_comparison": "The source semantics and checked Lean signature are pinned.",
        "lean_evidence": "The current configured declaration has the pinned elaborated signature.",
        "source_target_disposition": disposition,
        # Preserve an old route on purpose; it is not consulted in schema 2.
        "source_map_item_keys": [str(identity["source_key"])],
        "semantic_association_sha256": association[
            "semantic_association_sha256"
        ],
    }
    if corrected:
        target = corrected_target()
        response["governing_defect_ids"] = [DEFECT_ID]
        response["corrected_target_sha256_by_source_semantic_sha256"] = {
            identity["source_semantic_sha256"]: target["corrected_target_sha256"]
        }
    return response


class TargetDispositionUnitTests(unittest.TestCase):
    def test_current_source_correction_identity_index_is_fail_closed(self) -> None:
        uncorrected = DISPOSITION.current_source_correction_identity_by_key(
            statement_map(corrected=False), fidelity_ledger()
        )
        self.assertIn(SOURCE_KEY, uncorrected)
        self.assertIsNone(uncorrected[SOURCE_KEY])

        corrected = DISPOSITION.current_source_correction_identity_by_key(
            statement_map(corrected=True), fidelity_ledger()
        )
        target = corrected_target()
        self.assertEqual(
            corrected[SOURCE_KEY],
            {
                "corrected_target_sha256": target["corrected_target_sha256"],
                "governing_defect_ids": (DEFECT_ID,),
            },
        )

        stale_ledger = DISPOSITION.current_source_correction_identity_by_key(
            statement_map(corrected=True),
            fidelity_ledger(corrected_resolution="repaired_in_lean"),
        )
        self.assertNotIn(SOURCE_KEY, stale_ledger)

        stale_target_map = statement_map(corrected=True)
        stale_item = stale_target_map["items"][SOURCE_KEY]
        assert isinstance(stale_item, dict)
        stale_target = stale_item["corrected_target"]
        assert isinstance(stale_target, dict)
        stale_target["corrected_target_sha256"] = "0" * 64
        self.assertNotIn(
            SOURCE_KEY,
            DISPOSITION.current_source_correction_identity_by_key(
                stale_target_map, fidelity_ledger()
            ),
        )

    def test_supplemental_convention_scope_selects_exact_nonnamed_direct_route(
        self,
    ) -> None:
        source_map, item, association = supplemental_direct_route_fixture()
        ledger = supplemental_scope_ledger()

        errors = DISPOSITION.semantic_target_disposition_errors(
            item,
            source_convention_dimension_response(association, ledger),
            statement_map=source_map,
            source_proof_fidelity=ledger,
        )

        self.assertEqual(errors, [])

    def test_supplemental_direct_route_requires_a_ledger_selection(self) -> None:
        source_map, item, association = supplemental_direct_route_fixture()
        ledger = fidelity_ledger()

        errors = DISPOSITION.semantic_target_disposition_errors(
            item,
            source_convention_dimension_response(association, ledger),
            statement_map=source_map,
            source_proof_fidelity=ledger,
        )

        self.assertTrue(any("not selected" in error for error in errors), errors)

    def test_vocabulary_direct_route_requires_its_generated_selector_receipt(
        self,
    ) -> None:
        source_map, item, association = vocabulary_direct_route_fixture()
        response = schema_two_dimension_response(association)

        without_receipt = DISPOSITION.semantic_target_disposition_errors(
            item,
            response,
            statement_map=source_map,
            source_proof_fidelity=fidelity_ledger(),
        )
        self.assertTrue(
            any("not selected" in error for error in without_receipt),
            without_receipt,
        )

        with_receipt = DISPOSITION.semantic_target_disposition_errors(
            item,
            response,
            statement_map=source_map,
            source_proof_fidelity=fidelity_ledger(),
            validated_vocabulary_binding_source_item_ids=[SOURCE_KEY],
            validated_vocabulary_direct_route_source_item_ids=[SOURCE_KEY],
        )
        self.assertEqual(with_receipt, [])

    def test_vocabulary_binding_without_one_route_selector_rejects_deep_direct_credit(
        self,
    ) -> None:
        """A multi-route vocabulary definition cannot retain a stale direct association."""

        source_map, item, association = vocabulary_direct_route_fixture()
        source_map["source_coverage_mode"] = "deep_paper_with_all_prose_claims"
        source_item = source_map["items"][SOURCE_KEY]
        assert isinstance(source_item, dict)
        source_item["lean_declarations"] = [
            "Fixture.Paper.endpoint",
            "Fixture.Paper.otherEndpoint",
        ]
        errors = DISPOSITION.semantic_target_disposition_errors(
            item,
            schema_two_dimension_response(association),
            statement_map=source_map,
            source_proof_fidelity=fidelity_ledger(),
            validated_vocabulary_binding_source_item_ids=[SOURCE_KEY],
            validated_vocabulary_direct_route_source_item_ids=[],
        )

        self.assertTrue(any("not selected" in error for error in errors), errors)

    def test_vocabulary_direct_subset_must_belong_to_its_binding_selector(self) -> None:
        source_map, item, association = vocabulary_direct_route_fixture()
        errors = DISPOSITION.semantic_target_disposition_errors(
            item,
            schema_two_dimension_response(association),
            statement_map=source_map,
            source_proof_fidelity=fidelity_ledger(),
            validated_vocabulary_direct_route_source_item_ids=[SOURCE_KEY],
        )

        self.assertTrue(
            any("absent from the validated vocabulary binding selector" in error for error in errors),
            errors,
        )

    def test_legacy_direct_route_treats_absent_and_empty_vocabulary_receipts_equally(
        self,
    ) -> None:
        """An unrelated historical raw needs no migration for this selector."""

        source_map = legacy_direct_statement_map(corrected=False)
        item = legacy_direct_statement_semantic_item(corrected=False)
        association = item["source_statement_association"]
        assert isinstance(association, dict)
        response = schema_two_dimension_response(association)

        absent = DISPOSITION.semantic_target_disposition_errors(
            item,
            response,
            statement_map=source_map,
            source_proof_fidelity=fidelity_ledger(),
        )
        empty = DISPOSITION.semantic_target_disposition_errors(
            item,
            response,
            statement_map=source_map,
            source_proof_fidelity=fidelity_ledger(),
            validated_vocabulary_direct_route_source_item_ids=[],
        )
        self.assertEqual(absent, [])
        self.assertEqual(empty, absent)

    def test_supplemental_scope_cannot_suppress_named_claim_bearing_false(self) -> None:
        source_map, item, association = supplemental_direct_route_fixture(
            ordinary_named_presentation=True
        )
        ledger = supplemental_scope_ledger()

        errors = DISPOSITION.semantic_target_disposition_errors(
            item,
            source_convention_dimension_response(association, ledger),
            statement_map=source_map,
            source_proof_fidelity=ledger,
        )

        self.assertTrue(
            any("claim_bearing: false" in error for error in errors), errors
        )

    def test_supplemental_scope_rejects_absent_or_malformed_map_item(self) -> None:
        for replacement in (None, "not an object"):
            with self.subTest(replacement=replacement):
                source_map, item, association = supplemental_direct_route_fixture()
                items = source_map["items"]
                assert isinstance(items, dict)
                if replacement is None:
                    del items[SOURCE_KEY]
                else:
                    items[SOURCE_KEY] = replacement
                ledger = supplemental_scope_ledger()

                errors = DISPOSITION.semantic_target_disposition_errors(
                    item,
                    source_convention_dimension_response(association, ledger),
                    statement_map=source_map,
                    source_proof_fidelity=ledger,
                )

                self.assertTrue(
                    any("absent" in error or "not selected" in error for error in errors),
                    errors,
                )

    def test_claim_bearing_false_route_rejects_unrelated_or_malformed_scope_key(
        self,
    ) -> None:
        source_map, item, association = supplemental_direct_route_fixture()
        for scoped_source_key in ("different_source_item", None, 17):
            with self.subTest(scoped_source_key=scoped_source_key):
                ledger = supplemental_scope_ledger(source_key=scoped_source_key)
                errors = DISPOSITION.semantic_target_disposition_errors(
                    item,
                    source_convention_dimension_response(association, ledger),
                    statement_map=source_map,
                    source_proof_fidelity=ledger,
                )
                self.assertTrue(
                    any("not selected" in error for error in errors), errors
                )

    def test_schema_two_semantic_response_survives_map_key_rename(self) -> None:
        old_map = statement_map(corrected=False)
        old_source_item = old_map["items"][SOURCE_KEY]
        assert isinstance(old_source_item, dict)
        old_item = schema_two_semantic_item(SOURCE_KEY, old_source_item)
        old_association = old_item["semantic_contract_source_association"]
        assert isinstance(old_association, dict)
        response = schema_two_dimension_response(old_association)

        renamed_key = "renamed_source_route"
        current_map = statement_map(corrected=False, source_key=renamed_key)
        current_source_item = current_map["items"][renamed_key]
        assert isinstance(current_source_item, dict)
        current_item = schema_two_semantic_item(renamed_key, current_source_item)

        errors = DISPOSITION.semantic_target_disposition_errors(
            current_item,
            response,
            statement_map=current_map,
            source_proof_fidelity=fidelity_ledger(),
        )

        self.assertEqual(errors, [])

    def test_schema_two_corrected_semantic_response_uses_source_semantic_target_pin(
        self,
    ) -> None:
        old_map = statement_map(corrected=True)
        old_source_item = old_map["items"][SOURCE_KEY]
        assert isinstance(old_source_item, dict)
        old_item = schema_two_semantic_item(SOURCE_KEY, old_source_item)
        old_association = old_item["semantic_contract_source_association"]
        assert isinstance(old_association, dict)
        response = schema_two_dimension_response(old_association, corrected=True)

        renamed_key = "renamed_corrected_source_route"
        current_map = statement_map(corrected=True, source_key=renamed_key)
        current_source_item = current_map["items"][renamed_key]
        assert isinstance(current_source_item, dict)
        current_item = schema_two_semantic_item(renamed_key, current_source_item)

        errors = DISPOSITION.semantic_target_disposition_errors(
            current_item,
            response,
            statement_map=current_map,
            source_proof_fidelity=fidelity_ledger(),
        )

        self.assertEqual(errors, [])

    def test_selected_direct_route_binds_an_approved_corrected_target(self) -> None:
        source_map = legacy_direct_statement_map(corrected=True)
        item = legacy_direct_statement_semantic_item(corrected=True)
        association = item["source_statement_association"]
        assert isinstance(association, dict)
        response = schema_two_dimension_response(association, corrected=True)

        errors = DISPOSITION.semantic_target_disposition_errors(
            item,
            response,
            statement_map=source_map,
            source_proof_fidelity=fidelity_ledger(),
        )

        self.assertEqual(errors, [])

        response["source_target_disposition"] = "literal_source_match"
        response["verdict"] = "matches_literal_source"
        response.pop("governing_defect_ids")
        response.pop("corrected_target_sha256_by_source_semantic_sha256")
        errors = DISPOSITION.semantic_target_disposition_errors(
            item,
            response,
            statement_map=source_map,
            source_proof_fidelity=fidelity_ledger(),
        )
        self.assertTrue(any("cannot discharge" in error for error in errors), errors)

    def test_selected_direct_route_reuses_only_the_source_and_signature_identity(
        self,
    ) -> None:
        old_item = legacy_direct_statement_semantic_item(corrected=False)
        old_association = old_item["source_statement_association"]
        assert isinstance(old_association, dict)
        response = schema_two_dimension_response(old_association)

        renamed_key = "renamed_direct_source_route"
        current_map = legacy_direct_statement_map(
            corrected=False, source_key=renamed_key
        )
        current_item = legacy_direct_statement_semantic_item(
            corrected=False, source_key=renamed_key
        )
        current_association = current_item["source_statement_association"]
        assert isinstance(current_association, dict)
        self.assertEqual(
            old_association["semantic_association_sha256"],
            current_association["semantic_association_sha256"],
        )

        errors = DISPOSITION.semantic_target_disposition_errors(
            current_item,
            response,
            statement_map=current_map,
            source_proof_fidelity=fidelity_ledger(),
        )
        self.assertEqual(errors, [])

    def test_selected_direct_route_deduplicates_identical_route_metadata(self) -> None:
        source_map = legacy_direct_statement_map(corrected=False)
        source_item = source_map["items"][SOURCE_KEY]
        assert isinstance(source_item, dict)
        # A source-map author can record the same direct declaration both as
        # presentation coverage and as proof coverage.  It is still one route.
        source_item["proof_lean_declarations"] = ["Fixture.Paper.endpoint"]
        signature = reviewed_signature()
        association = SOURCE_AUDIT.explicit_direct_source_route_association(
            source_identities=[
                SOURCE_AUDIT.semantic_contract_source_identity(
                    SOURCE_KEY, source_item
                )
            ],
            reviewed_identity={
                "qualified_declaration": signature["qualified_declaration"],
                "declaration_sha256": "a" * 64,
            },
            reviewed_signature_identity=signature,
        )
        item = {
            "judgment_key": SEMANTIC_KEY,
            "row": "opaque_surface",
            "qualified_declaration": signature["qualified_declaration"],
            "source_statement_association": association,
        }

        errors = DISPOSITION.semantic_target_disposition_errors(
            item,
            schema_two_dimension_response(association),
            statement_map=source_map,
            source_proof_fidelity=fidelity_ledger(),
        )

        self.assertEqual(errors, [])

    def test_selected_direct_route_reuses_across_a_declaration_rename(self) -> None:
        old_item = legacy_direct_statement_semantic_item(corrected=False)
        old_association = old_item["source_statement_association"]
        assert isinstance(old_association, dict)
        response = schema_two_dimension_response(old_association)

        renamed_declaration = "Fixture.Paper.renamed_endpoint"
        current_map = legacy_direct_statement_map(
            corrected=False,
            qualified_declaration=renamed_declaration,
        )
        current_item = legacy_direct_statement_semantic_item(
            corrected=False,
            qualified_declaration=renamed_declaration,
        )
        current_association = current_item["source_statement_association"]
        assert isinstance(current_association, dict)
        self.assertEqual(
            old_association["semantic_association_sha256"],
            current_association["semantic_association_sha256"],
        )
        SOURCE_AUDIT.attach_source_record_item_digests(
            [old_item],
            paper_statement_map=legacy_direct_statement_map(corrected=False),
            source_proof_fidelity=fidelity_ledger(),
            row_qualified_names={"opaque_surface": "Fixture.Paper.endpoint"},
            elaborated_signature_sha256_by_qualified={
                "Fixture.Paper.endpoint": "b" * 64
            },
        )
        SOURCE_AUDIT.attach_source_record_item_digests(
            [current_item],
            paper_statement_map=current_map,
            source_proof_fidelity=fidelity_ledger(),
            row_qualified_names={"opaque_surface": renamed_declaration},
            elaborated_signature_sha256_by_qualified={renamed_declaration: "b" * 64},
        )
        self.assertEqual(
            old_item["source_record_item_sha256"],
            current_item["source_record_item_sha256"],
        )

        errors = DISPOSITION.semantic_target_disposition_errors(
            current_item,
            response,
            statement_map=current_map,
            source_proof_fidelity=fidelity_ledger(),
        )
        self.assertEqual(errors, [])

    def test_schema_two_semantic_response_requires_current_signature_pin(self) -> None:
        source_map = statement_map(corrected=False)
        source_item = source_map["items"][SOURCE_KEY]
        assert isinstance(source_item, dict)
        old_item = schema_two_semantic_item(SOURCE_KEY, source_item)
        old_association = old_item["semantic_contract_source_association"]
        assert isinstance(old_association, dict)
        response = schema_two_dimension_response(old_association)
        current_item = schema_two_semantic_item(
            SOURCE_KEY, source_item, signature=reviewed_signature(digest="c" * 64)
        )

        errors = DISPOSITION.semantic_target_disposition_errors(
            current_item,
            response,
            statement_map=source_map,
            source_proof_fidelity=fidelity_ledger(),
        )

        self.assertTrue(
            any("semantic_association_sha256" in error for error in errors), errors
        )

    def test_schema_two_semantic_response_fails_closed_without_signature_identity(self) -> None:
        source_map = statement_map(corrected=False)
        source_item = source_map["items"][SOURCE_KEY]
        assert isinstance(source_item, dict)
        item = schema_two_semantic_item(SOURCE_KEY, source_item)
        association = item["semantic_contract_source_association"]
        assert isinstance(association, dict)
        response = schema_two_dimension_response(association)
        association.pop("reviewed_elaborated_signature_identity")

        errors = DISPOSITION.semantic_target_disposition_errors(
            item,
            response,
            statement_map=source_map,
            source_proof_fidelity=fidelity_ledger(),
        )

        self.assertTrue(
            any("lacks reviewed_elaborated_signature_identity" in error for error in errors),
            errors,
        )

    def test_literal_source_match_accepts_only_uncorrected_identity(self) -> None:
        errors = DISPOSITION.semantic_target_disposition_errors(
            semantic_item(),
            dimension_response("literal_source_match"),
            statement_map=statement_map(corrected=False),
            source_proof_fidelity=fidelity_ledger(),
        )

        self.assertEqual(errors, [])

    def test_literal_source_match_cannot_erase_corrected_target(self) -> None:
        errors = DISPOSITION.semantic_target_disposition_errors(
            semantic_item(),
            dimension_response("literal_source_match"),
            statement_map=statement_map(corrected=True),
            source_proof_fidelity=fidelity_ledger(),
        )

        self.assertTrue(any("cannot discharge" in error for error in errors), errors)

    def test_convention_requires_current_ledger_identity(self) -> None:
        response = dimension_response("approved_source_convention")
        errors = DISPOSITION.semantic_target_disposition_errors(
            semantic_item(),
            response,
            statement_map=statement_map(corrected=False),
            source_proof_fidelity=fidelity_ledger(),
        )
        self.assertEqual(errors, [])

        response["model_convention_sha256_by_id"] = {CONVENTION_ID: "0" * 64}
        errors = DISPOSITION.semantic_target_disposition_errors(
            semantic_item(),
            response,
            statement_map=statement_map(corrected=False),
            source_proof_fidelity=fidelity_ledger(),
        )
        self.assertTrue(
            any("current model-convention digest" in error for error in errors),
            errors,
        )

        response["model_convention_ids"] = ["UNKNOWN-CONVENTION"]
        errors = DISPOSITION.semantic_target_disposition_errors(
            semantic_item(),
            response,
            statement_map=statement_map(corrected=False),
            source_proof_fidelity=fidelity_ledger(),
        )
        self.assertTrue(any("unknown" in error for error in errors), errors)

    def test_convention_semantic_digest_excludes_field_scope_routing_only(self) -> None:
        """A field-route attachment must not reopen a model comparison."""

        ledger = fidelity_ledger()
        conventions = ledger["model_conventions"]
        assert isinstance(conventions, list) and len(conventions) == 1
        convention = conventions[0]
        assert isinstance(convention, dict)
        scoped = dict(convention)
        scoped["recursive_field_source_scope"] = {
            "schema": 1,
            "entries": [
                {
                    "source_item": SOURCE_KEY,
                    "root_record": "Fixture.Model",
                    "field_chain": [
                        {"structure": "Fixture.Model", "field": "rate"}
                    ],
                    "source_locator": "source.tex:10",
                    "permitted_classifications": ["validated_source_assumption"],
                }
            ],
        }

        self.assertEqual(
            DISPOSITION.model_convention_semantic_digest(convention),
            DISPOSITION.model_convention_semantic_digest(scoped),
        )
        self.assertNotEqual(
            DISPOSITION.model_convention_record_digest(convention),
            DISPOSITION.model_convention_record_digest(scoped),
        )
        changed_meaning = dict(scoped)
        changed_meaning["formal_meaning"] = "A distinct source model."
        self.assertNotEqual(
            DISPOSITION.model_convention_semantic_digest(convention),
            DISPOSITION.model_convention_semantic_digest(changed_meaning),
        )

    def test_corrected_target_requires_exact_defect_resolution_and_target_digest(self) -> None:
        response = dimension_response("approved_corrected_target", corrected=True)
        errors = DISPOSITION.semantic_target_disposition_errors(
            semantic_item(),
            response,
            statement_map=statement_map(corrected=True),
            source_proof_fidelity=fidelity_ledger(),
        )
        self.assertEqual(errors, [])

        errors = DISPOSITION.semantic_target_disposition_errors(
            semantic_item(),
            response,
            statement_map=statement_map(corrected=True),
            source_proof_fidelity=fidelity_ledger(corrected_resolution="repaired_in_lean"),
        )
        self.assertTrue(
            any("must resolve as corrected_source_statement" in error for error in errors),
            errors,
        )

    def test_historical_corrected_target_requires_or_uses_archived_map_snapshot(self) -> None:
        response = dimension_response("approved_corrected_target", corrected=True)
        errors = DISPOSITION.semantic_target_disposition_errors(
            semantic_item(),
            response,
            statement_map=None,
            source_proof_fidelity=fidelity_ledger(),
            historical_receipt_only=True,
        )
        self.assertTrue(any("full archived source-map" in error for error in errors), errors)
        errors = DISPOSITION.semantic_target_disposition_errors(
            semantic_item(),
            response,
            statement_map=statement_map(corrected=True),
            source_proof_fidelity=fidelity_ledger(),
            historical_receipt_only=True,
        )
        self.assertEqual(errors, [])

    def test_bare_source_model_verdict_cannot_mask_a_corrected_target(self) -> None:
        response = dimension_response("approved_corrected_target", corrected=True)
        response["verdict"] = "matches_source_model"

        errors = DISPOSITION.semantic_target_disposition_errors(
            semantic_item(),
            response,
            statement_map=statement_map(corrected=True),
            source_proof_fidelity=fidelity_ledger(),
        )

        self.assertTrue(
            any("must use semantic verdict" in error for error in errors), errors
        )


class InputTargetDispositionUnitTests(unittest.TestCase):
    def test_generator_schema_two_association_matches_shared_validator(self) -> None:
        source_item = statement_map(corrected=False)["items"][SOURCE_KEY]
        assert isinstance(source_item, dict)
        source_identity = SOURCE_AUDIT.semantic_contract_source_identity(
            SOURCE_KEY, source_item
        )
        declaration_identity = SOURCE_AUDIT.reviewed_declaration_identity(
            "Fixture.Paper.endpoint",
            "theorem endpoint (x : Nat) (h : Ready x) : Wins x := by sorry",
        )
        assert declaration_identity is not None
        signature = reviewed_signature()
        association = SOURCE_AUDIT.source_contract_association_payload(
            association_mode="semantic_contract_group_member",
            semantic_model_judgment_key=SEMANTIC_KEY,
            member_role="direct_evidence",
            reviewed_identity=declaration_identity,
            source_identities=[source_identity],
            reviewed_signature_identity=signature,
        )
        self.assertEqual(association["schema"], 2)
        item = {
            "judgment_key": "endpoint.hcondition",
            "source_contract_association": association,
        }
        response = schema_two_input_response(association)

        errors = DISPOSITION.source_input_target_disposition_errors(
            item,
            response,
            statement_map=statement_map(corrected=False),
            source_proof_fidelity=fidelity_ledger(),
        )

        self.assertEqual(errors, [])

    def test_schema_two_input_response_survives_map_key_rename(self) -> None:
        old_map = statement_map(corrected=False)
        old_source_item = old_map["items"][SOURCE_KEY]
        assert isinstance(old_source_item, dict)
        old_item = schema_two_input_item(SOURCE_KEY, old_source_item)
        old_association = old_item["source_contract_association"]
        assert isinstance(old_association, dict)
        response = schema_two_input_response(old_association)

        renamed_key = "renamed_source_route"
        current_map = statement_map(corrected=False, source_key=renamed_key)
        current_source_item = current_map["items"][renamed_key]
        assert isinstance(current_source_item, dict)
        current_item = schema_two_input_item(renamed_key, current_source_item)

        errors = DISPOSITION.source_input_target_disposition_errors(
            current_item,
            response,
            statement_map=current_map,
            source_proof_fidelity=fidelity_ledger(),
        )

        self.assertEqual(errors, [])

    def test_schema_two_corrected_input_uses_source_semantic_target_pin(self) -> None:
        old_map = statement_map(corrected=True)
        old_source_item = old_map["items"][SOURCE_KEY]
        assert isinstance(old_source_item, dict)
        old_item = schema_two_input_item(SOURCE_KEY, old_source_item)
        old_association = old_item["source_contract_association"]
        assert isinstance(old_association, dict)
        response = schema_two_input_response(old_association, corrected=True)

        renamed_key = "renamed_corrected_source_route"
        current_map = statement_map(corrected=True, source_key=renamed_key)
        current_source_item = current_map["items"][renamed_key]
        assert isinstance(current_source_item, dict)
        current_item = schema_two_input_item(renamed_key, current_source_item)

        errors = DISPOSITION.source_input_target_disposition_errors(
            current_item,
            response,
            statement_map=current_map,
            source_proof_fidelity=fidelity_ledger(),
        )

        self.assertEqual(errors, [])

    def test_schema_two_input_rejects_stale_or_missing_semantic_pin(self) -> None:
        source_map = statement_map(corrected=False)
        source_item = source_map["items"][SOURCE_KEY]
        assert isinstance(source_item, dict)
        item = schema_two_input_item(SOURCE_KEY, source_item)
        association = item["source_contract_association"]
        assert isinstance(association, dict)
        response = schema_two_input_response(association)
        response.pop("semantic_association_sha256")

        errors = DISPOSITION.source_input_target_disposition_errors(
            item,
            response,
            statement_map=source_map,
            source_proof_fidelity=fidelity_ledger(),
        )

        self.assertTrue(
            any("semantic_association_sha256" in error for error in errors), errors
        )

    def test_schema_two_input_rejects_ambiguous_source_semantic_identity(self) -> None:
        source_map = statement_map(corrected=False)
        duplicate_key = "duplicate_semantic_source"
        duplicate_item = dict(source_map["items"][SOURCE_KEY])
        source_map["items"][duplicate_key] = duplicate_item
        source_item = source_map["items"][SOURCE_KEY]
        assert isinstance(source_item, dict)
        item = schema_two_input_item(SOURCE_KEY, source_item)
        association = item["source_contract_association"]
        assert isinstance(association, dict)
        response = schema_two_input_response(association)
        duplicate_identity = schema_two_source_identity(duplicate_key, duplicate_item)
        identities = association["source_item_identities"]
        assert isinstance(identities, list)
        identities.append(duplicate_identity)
        association["source_map_item_keys"] = [SOURCE_KEY, duplicate_key]
        association["source_map_item_sha256_by_key"] = {
            SOURCE_KEY: identities[0]["source_map_item_sha256"],
            duplicate_key: duplicate_identity["source_map_item_sha256"],
        }
        association["source_map_item_keys_sha256"] = (
            DISPOSITION.source_map_item_record_digest([SOURCE_KEY, duplicate_key])
        )
        signature = association["reviewed_elaborated_signature_identity"]
        assert isinstance(signature, dict)
        association["semantic_association_sha256"] = (
            DISPOSITION.semantic_association_record_digest(
                [
                    identities[0]["source_semantic_sha256"],
                    duplicate_identity["source_semantic_sha256"],
                ],
                signature,
            )
        )
        association["association_sha256"] = (
            DISPOSITION.source_contract_association_record_digest(association)
        )

        errors = DISPOSITION.source_input_target_disposition_errors(
            item,
            response,
            statement_map=source_map,
            source_proof_fidelity=fidelity_ledger(),
        )

        self.assertTrue(any("ambiguous duplicate" in error for error in errors), errors)

    def test_generator_association_hashes_are_accepted_by_shared_validator(self) -> None:
        source_item = statement_map(corrected=False)["items"][SOURCE_KEY]
        source_identity = SOURCE_AUDIT.semantic_contract_source_identity(
            SOURCE_KEY, source_item
        )
        declaration_identity = SOURCE_AUDIT.reviewed_declaration_identity(
            "Fixture.Paper.endpoint",
            "theorem endpoint (x : Nat) (h : Ready x) : Wins x := by sorry",
        )
        assert declaration_identity is not None
        association = SOURCE_AUDIT.source_contract_association_payload(
            association_mode="semantic_contract_group_member",
            semantic_model_judgment_key=SEMANTIC_KEY,
            member_role="direct_evidence",
            reviewed_identity=declaration_identity,
            source_identities=[source_identity],
        )
        item = {
            "judgment_key": "endpoint.hcondition",
            "source_contract_association": association,
        }
        response = input_response("validated_source_assumption")
        response["source_contract_association_sha256"] = association[
            "association_sha256"
        ]
        response["source_map_item_sha256_by_key"] = association[
            "source_map_item_sha256_by_key"
        ]

        errors = DISPOSITION.source_input_target_disposition_errors(
            item,
            response,
            statement_map=statement_map(corrected=False),
            source_proof_fidelity=fidelity_ledger(),
        )

        self.assertEqual(errors, [])

    def test_convention_and_corrected_input_conditions_require_pinned_targets(self) -> None:
        convention = input_response("approved_source_convention")
        errors = DISPOSITION.source_input_target_disposition_errors(
            source_contract_input_item(corrected=False),
            convention,
            statement_map=statement_map(corrected=False),
            source_proof_fidelity=fidelity_ledger(),
            status="formalized",
        )
        self.assertEqual(errors, [])

        convention["model_convention_sha256_by_id"] = {CONVENTION_ID: "0" * 64}
        errors = DISPOSITION.source_input_target_disposition_errors(
            source_contract_input_item(corrected=False),
            convention,
            statement_map=statement_map(corrected=False),
            source_proof_fidelity=fidelity_ledger(),
            status="formalized",
        )
        self.assertTrue(any("current model-convention digest" in error for error in errors), errors)

        convention = input_response("approved_source_convention")
        convention["model_convention_ids"] = ["STALE-CONVENTION-ID"]
        convention["model_convention_sha256_by_id"] = {
            "STALE-CONVENTION-ID": "0" * 64
        }
        errors = DISPOSITION.source_input_target_disposition_errors(
            source_contract_input_item(corrected=False),
            convention,
            statement_map=statement_map(corrected=False),
            source_proof_fidelity=fidelity_ledger(),
            status="formalized",
        )
        self.assertTrue(any("unknown" in error for error in errors), errors)

        corrected = input_response("approved_corrected_condition", corrected=True)
        errors = DISPOSITION.source_input_target_disposition_errors(
            source_contract_input_item(corrected=True),
            corrected,
            statement_map=statement_map(corrected=True),
            source_proof_fidelity=fidelity_ledger(),
            status="formalized",
        )
        self.assertEqual(errors, [])

        corrected["corrected_target_sha256_by_source_item"] = {SOURCE_KEY: "0" * 64}
        errors = DISPOSITION.source_input_target_disposition_errors(
            source_contract_input_item(corrected=True),
            corrected,
            statement_map=statement_map(corrected=True),
            source_proof_fidelity=fidelity_ledger(),
            status="formalized",
        )
        self.assertTrue(any("current corrected-target digest" in error for error in errors), errors)

        corrected = input_response("approved_corrected_condition", corrected=True)
        corrected["governing_defect_ids"] = ["STALE-DEFECT-ID"]
        errors = DISPOSITION.source_input_target_disposition_errors(
            source_contract_input_item(corrected=True),
            corrected,
            statement_map=statement_map(corrected=True),
            source_proof_fidelity=fidelity_ledger(),
            status="formalized",
        )
        self.assertTrue(any("governing_defect_ids" in error for error in errors), errors)

    def test_historical_corrected_input_requires_or_uses_archived_map_snapshot(self) -> None:
        response = input_response("approved_corrected_condition", corrected=True)
        errors = DISPOSITION.source_input_target_disposition_errors(
            source_contract_input_item(corrected=True),
            response,
            statement_map=None,
            source_proof_fidelity=fidelity_ledger(),
            historical_receipt_only=True,
        )
        self.assertTrue(any("full archived source-map" in error for error in errors), errors)
        errors = DISPOSITION.source_input_target_disposition_errors(
            source_contract_input_item(corrected=True),
            response,
            statement_map=statement_map(corrected=True),
            source_proof_fidelity=fidelity_ledger(),
            historical_receipt_only=True,
        )
        self.assertEqual(errors, [])

    def test_approved_convention_antecedent_is_pinned_and_nonconstructive(self) -> None:
        item = source_contract_input_item(corrected=False)
        response = input_response("approved_source_convention")
        kwargs = {
            "statement_map": statement_map(corrected=False),
            "source_proof_fidelity": fidelity_ledger(),
            "status": "formalized",
        }

        self.assertEqual(
            DISPOSITION.approved_source_convention_antecedent_errors(
                item, response, **kwargs
            ),
            [],
        )

        missing_locator = dict(response)
        missing_locator.pop("source_location")
        errors = DISPOSITION.approved_source_convention_antecedent_errors(
            item, missing_locator, **kwargs
        )
        self.assertTrue(any("exact source location" in error for error in errors), errors)

        stale_ledger = dict(response)
        stale_ledger["model_convention_sha256_by_id"] = {CONVENTION_ID: "0" * 64}
        errors = DISPOSITION.approved_source_convention_antecedent_errors(
            item, stale_ledger, **kwargs
        )
        self.assertTrue(any("current model-convention digest" in error for error in errors), errors)

        conclusion_package = dict(item)
        conclusion_package["conclusion_fields"] = [{"judgment_key": "Fixture.Model.result"}]
        errors = DISPOSITION.approved_source_convention_antecedent_errors(
            conclusion_package, response, **kwargs
        )
        self.assertTrue(any("conclusion-bearing" in error for error in errors), errors)

        constructor_result = dict(item)
        constructor_result["conditional_constructors"] = [{"declaration": "Fixture.build"}]
        errors = DISPOSITION.approved_source_convention_antecedent_errors(
            constructor_result, response, **kwargs
        )
        self.assertTrue(any("constructor-derived" in error for error in errors), errors)

    def test_repository_current_convention_route_rejects_result_bearing_inputs(self) -> None:
        item = source_contract_input_item(corrected=False)
        item.update(
            {
                "kind": "aliased_conclusion_bridge_input",
                "conclusion_fields": [],
                "valid_constructors": [],
                "conditional_constructors": [],
                "rejected_constructors": [],
                # A theorem may consume this premise while proving the result;
                # that use is not itself a result-bearing field or package.
                "result_bridges": [
                    {
                        "input_relation": "component_of_target",
                        "result_relation": "equivalent",
                    }
                ],
            }
        )
        response = input_response("approved_source_convention")
        response["source_record_audit_sha256"] = "current-audit-digest"
        kwargs = {
            "digest": "current-audit-digest",
            "expected_item_digests": {},
            "expected_item_digest_pins": {},
            "statement_map": statement_map(corrected=False),
            "source_proof_fidelity": fidelity_ledger(),
            "status": "formalized",
        }

        self.assertTrue(
            REPOSITORY.current_approved_source_convention_antecedent(
                item, response, **kwargs
            )
        )

        result_field = dict(item)
        result_field["conclusion_fields"] = [
            {"judgment_key": "Fixture.Model.result"}
        ]
        self.assertFalse(
            REPOSITORY.current_approved_source_convention_antecedent(
                result_field, response, **kwargs
            )
        )

        constructor = dict(item)
        constructor["conditional_constructors"] = [{"declaration": "Fixture.build"}]
        self.assertFalse(
            REPOSITORY.current_approved_source_convention_antecedent(
                constructor, response, **kwargs
            )
        )

        result_relation = dict(item)
        result_relation["result_relation"] = "equivalent"
        self.assertFalse(
            REPOSITORY.current_approved_source_convention_antecedent(
                result_relation, response, **kwargs
            )
        )

        stale = dict(response)
        stale["source_record_audit_sha256"] = "stale-audit-digest"
        self.assertFalse(
            REPOSITORY.current_approved_source_convention_antecedent(
                item, stale, **kwargs
            )
        )

        literal = input_response("validated_source_assumption")
        literal["source_record_audit_sha256"] = "current-audit-digest"
        self.assertFalse(
            REPOSITORY.current_approved_source_convention_antecedent(
                item, literal, **kwargs
            )
        )

    def test_stale_association_or_source_map_digest_fails(self) -> None:
        response = input_response("validated_source_assumption")
        response["source_contract_association_sha256"] = "0" * 64
        errors = DISPOSITION.source_input_target_disposition_errors(
            source_contract_input_item(corrected=False),
            response,
            statement_map=statement_map(corrected=False),
            source_proof_fidelity=fidelity_ledger(),
        )
        self.assertTrue(any("source_contract_association_sha256" in error for error in errors), errors)

        response = input_response("validated_source_assumption")
        response["source_map_item_sha256_by_key"] = {SOURCE_KEY: "0" * 64}
        errors = DISPOSITION.source_input_target_disposition_errors(
            source_contract_input_item(corrected=False),
            response,
            statement_map=statement_map(corrected=False),
            source_proof_fidelity=fidelity_ledger(),
        )
        self.assertTrue(any("source_map_item_sha256_by_key" in error for error in errors), errors)

        changed_map = statement_map(corrected=False)
        changed_map["items"][SOURCE_KEY]["source_kind"] = "changed theorem kind"
        errors = DISPOSITION.source_input_target_disposition_errors(
            source_contract_input_item(corrected=False),
            input_response("validated_source_assumption"),
            statement_map=changed_map,
            source_proof_fidelity=fidelity_ledger(),
        )
        self.assertTrue(any("current source-map item SHA-256" in error for error in errors), errors)

    def test_corrected_input_cannot_claim_archival_literal_target(self) -> None:
        response = input_response("validated_source_assumption", corrected=True)
        response["source_target_disposition"] = "literal_source_match"
        response.pop("governing_defect_ids", None)
        response.pop("corrected_target_sha256_by_source_item", None)
        errors = DISPOSITION.source_input_target_disposition_errors(
            source_contract_input_item(corrected=True),
            response,
            statement_map=statement_map(corrected=True),
            source_proof_fidelity=fidelity_ledger(),
        )
        self.assertTrue(any("cannot claim archival literal" in error for error in errors), errors)

    def test_external_boundary_is_partial_only(self) -> None:
        response = {"classification": "approved_external_boundary"}
        errors = DISPOSITION.source_input_target_disposition_errors(
            source_contract_input_item(corrected=False),
            response,
            statement_map=statement_map(corrected=False),
            source_proof_fidelity=fidelity_ledger(),
            status="formalized",
        )
        self.assertTrue(any("partial-only" in error for error in errors), errors)


class TargetDispositionIntegrationTests(unittest.TestCase):
    def test_repository_semantic_model_gate_uses_shared_corrected_target_validator(self) -> None:
        item = semantic_item()
        judgment = semantic_judgment(dimension_response("literal_source_match"))
        findings = REPOSITORY.semantic_model_review_findings(
            "Fixture",
            Path("Fixture"),
            Path("Fixture/audit/source_record_match_llm.json"),
            [item],
            {SEMANTIC_KEY: judgment},
            digest="current-audit-digest",
            expected_item_digests={SEMANTIC_KEY: "semantic-item-digest"},
            severity="ERROR",
            target_disposition_statement_map=statement_map(corrected=True),
            target_disposition_source_proof_fidelity=fidelity_ledger(),
            enforce_target_disposition=True,
        )

        self.assertTrue(
            any("invalid source target disposition" in finding.message for finding in findings),
            [finding.message for finding in findings],
        )

    def test_evidence_gate_uses_shared_validator_and_skips_pre_v10_records(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            paper = root / "papers" / "Fixture"
            audit = paper / "audit"
            audit.mkdir(parents=True)
            previous_root = EVIDENCE.ROOT
            EVIDENCE.ROOT = root
            self.addCleanup(setattr, EVIDENCE, "ROOT", previous_root)

            (paper / "status.json").write_text(
                json.dumps(
                    {
                        "status": "formalized",
                        "review_surface": {
                            "llm_source_record_review": {
                                "source_record_audit_file": "papers/Fixture/audit/source_record_audit.json",
                                "source_record_judgment_file": "papers/Fixture/audit/source_record_match_llm.json",
                            },
                            "source_proof_fidelity_review": {
                                "ledger_file": "papers/Fixture/audit/source_proof_fidelity.json"
                            },
                        },
                    }
                ),
                encoding="utf-8",
            )
            (audit / "paper_statement_map.json").write_text(
                json.dumps(statement_map(corrected=True)), encoding="utf-8"
            )
            (audit / "source_proof_fidelity.json").write_text(
                json.dumps(fidelity_ledger()), encoding="utf-8"
            )
            record = {
                "prompt_version": PROMPT_VERSION,
                "source_record_audit_sha256": "current-audit-digest",
                "paper_statement_map_sha256": (
                    EVIDENCE.current_paper_statement_map_sha256(paper)
                ),
                "source_record_input_fingerprint": {
                    "max_depth": 4,
                    "no_lean": False,
                },
                "semantic_model_items": [semantic_item()],
            }
            complete_v10_scan_fixture(record, has_surface=True)
            stamp_source_record_audit_receipts(record)
            (audit / "source_record_audit.json").write_text(
                json.dumps(record), encoding="utf-8"
            )
            match = {
                "schema": 1,
                "prompt_version": PROMPT_VERSION,
                "source_record_audit_sha256": "current-audit-digest",
                "validator": "fixture-reviewer",
                "validated_at": "2026-07-26T00:00:00Z",
                "items": {
                    SEMANTIC_KEY: semantic_judgment(
                        dimension_response("literal_source_match")
                    )
                },
            }
            match["source_record_audit_sha256"] = record[
                "source_record_audit_sha256"
            ]
            semantic_match = match["items"][SEMANTIC_KEY]
            assert isinstance(semantic_match, dict)
            semantic_match["source_record_audit_sha256"] = record[
                "source_record_audit_sha256"
            ]
            (audit / "source_record_match_llm.json").write_text(
                json.dumps(match), encoding="utf-8"
            )

            with patch.object(
                EVIDENCE,
                "source_record_current_input_fingerprint_error",
                return_value="",
            ):
                findings = EVIDENCE.source_record_semantic_target_disposition_findings(
                    paper, "formalized"
                )
            self.assertTrue(
                any("literal_source_match cannot discharge" in finding.message for finding in findings),
                [finding.message for finding in findings],
            )

            record["prompt_version"] = "source-record-v8-qualified-corrected-contract"
            (audit / "source_record_audit.json").write_text(
                json.dumps(record), encoding="utf-8"
            )
            self.assertEqual(
                EVIDENCE.source_record_semantic_target_disposition_findings(
                    paper, "formalized"
                ),
                [],
            )


class InputTargetDispositionIntegrationTests(unittest.TestCase):
    def source_record_payload(self, *, corrected: bool) -> dict[str, object]:
        item = source_contract_input_item(corrected=corrected)
        key = str(item["judgment_key"])
        payload: dict[str, object] = {
            "prompt_version": PROMPT_VERSION,
            "source_record_audit_sha256": "current-audit-digest",
            "source_record_input_fingerprint": {
                "max_depth": 4,
                "no_lean": False,
            },
            "boundary_input_count": 1,
            "recursive_field_count": 0,
            "rows_with_record_premises": [],
            "expected_input_judgment_keys": [key],
            "expected_field_judgment_keys": [],
            "expected_semantic_model_judgment_keys": [],
            "boundary_input_items": [item],
            "conclusion_dependency_items": [],
            "recursive_field_items": [],
            "semantic_model_items": [],
        }
        complete_v10_scan_fixture(payload, has_surface=True)
        return payload

    def source_record_match(self, response: dict[str, object]) -> dict[str, object]:
        return {
            "schema": 1,
            "paper": "Fixture",
            "prompt_version": PROMPT_VERSION,
            "source_record_audit_sha256": "current-audit-digest",
            "validator": "fixture-reviewer",
            "validated_at": "2026-07-26T00:00:00Z",
            "items": {"endpoint.hcondition": response},
        }

    def test_repository_gate_rejects_literal_credit_for_corrected_input(self) -> None:
        payload = self.source_record_payload(corrected=True)
        response = input_response("validated_source_assumption", corrected=True)
        response["source_target_disposition"] = "literal_source_match"
        response.pop("governing_defect_ids", None)
        response.pop("corrected_target_sha256_by_source_item", None)
        old_helper = REPOSITORY.run_source_record_audit_helper
        with tempfile.TemporaryDirectory() as temporary:
            folder = Path(temporary) / "Fixture"
            audit = folder / "audit"
            audit.mkdir(parents=True)
            (folder / "status.json").write_text(
                json.dumps({"status": "formalized"}), encoding="utf-8"
            )
            (audit / "paper_statement_map.json").write_text(
                json.dumps(statement_map(corrected=True)), encoding="utf-8"
            )
            (audit / "source_proof_fidelity.json").write_text(
                json.dumps(fidelity_ledger()), encoding="utf-8"
            )
            (audit / "source_record_audit.json").write_text(
                json.dumps(payload), encoding="utf-8"
            )
            (audit / "source_record_match_llm.json").write_text(
                json.dumps(self.source_record_match(response)), encoding="utf-8"
            )
            try:
                REPOSITORY.run_source_record_audit_helper = lambda _paper: (payload, "")
                findings = REPOSITORY.check_source_record_audit(
                    "Fixture", folder, {}, "formalized", strict_assumption_policy=True
                )
            finally:
                REPOSITORY.run_source_record_audit_helper = old_helper

        self.assertTrue(
            any("invalid source input target disposition" in finding.message for finding in findings),
            [finding.message for finding in findings],
        )

    def test_evidence_gate_rejects_stale_input_association_digest(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            paper = root / "papers" / "Fixture"
            audit = paper / "audit"
            audit.mkdir(parents=True)
            previous_root = EVIDENCE.ROOT
            EVIDENCE.ROOT = root
            self.addCleanup(setattr, EVIDENCE, "ROOT", previous_root)
            payload = self.source_record_payload(corrected=False)
            response = input_response("approved_source_convention")
            response["source_contract_association_sha256"] = "0" * 64
            (paper / "status.json").write_text(
                json.dumps({"status": "formalized"}), encoding="utf-8"
            )
            (audit / "paper_statement_map.json").write_text(
                json.dumps(statement_map(corrected=False)), encoding="utf-8"
            )
            (audit / "source_proof_fidelity.json").write_text(
                json.dumps(fidelity_ledger()), encoding="utf-8"
            )
            payload["paper_statement_map_sha256"] = (
                EVIDENCE.current_paper_statement_map_sha256(paper)
            )
            stamp_source_record_audit_receipts(payload)
            (audit / "source_record_audit.json").write_text(
                json.dumps(payload), encoding="utf-8"
            )
            match = self.source_record_match(response)
            match["source_record_audit_sha256"] = payload[
                "source_record_audit_sha256"
            ]
            (audit / "source_record_match_llm.json").write_text(
                json.dumps(match), encoding="utf-8"
            )

            with patch.object(
                EVIDENCE,
                "source_record_current_input_fingerprint_error",
                return_value="",
            ):
                findings = EVIDENCE.source_record_input_target_disposition_findings(
                    paper, "formalized"
                )

        self.assertTrue(
            any("source_contract_association_sha256" in finding.message for finding in findings),
            [finding.message for finding in findings],
        )

    def test_evidence_gate_requires_v10_association_schema_for_direct_routes(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            paper = root / "papers" / "Fixture"
            audit = paper / "audit"
            audit.mkdir(parents=True)
            previous_root = EVIDENCE.ROOT
            EVIDENCE.ROOT = root
            self.addCleanup(setattr, EVIDENCE, "ROOT", previous_root)
            payload = self.source_record_payload(corrected=False)
            direct_map = statement_map(corrected=False)
            direct_map["items"][SOURCE_KEY]["claim_bearing"] = True
            direct_map["items"][SOURCE_KEY]["semantic_contract"] = {
                "evidence_declaration": "Fixture.Paper.endpoint",
                "spec_declaration": "Fixture.Paper.endpointSpec",
            }
            (paper / "status.json").write_text(
                json.dumps({"status": "formalized"}), encoding="utf-8"
            )
            (audit / "paper_statement_map.json").write_text(
                json.dumps(direct_map), encoding="utf-8"
            )
            (audit / "source_proof_fidelity.json").write_text(
                json.dumps(fidelity_ledger()), encoding="utf-8"
            )
            payload["paper_statement_map_sha256"] = (
                EVIDENCE.current_paper_statement_map_sha256(paper)
            )
            (audit / "source_record_audit.json").write_text(
                json.dumps(payload), encoding="utf-8"
            )
            (audit / "source_record_match_llm.json").write_text(
                json.dumps(
                    self.source_record_match(
                        input_response("validated_source_assumption")
                    )
                ),
                encoding="utf-8",
            )

            findings = EVIDENCE.source_record_input_target_disposition_findings(
                paper, "formalized"
            )

        self.assertTrue(
            any("no generated declaration-content source-contract association schema" in finding.message for finding in findings),
            [finding.message for finding in findings],
        )

    def test_evidence_gate_rejects_legacy_direct_routes_without_generated_inventory(
        self,
    ) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            paper = root / "papers" / "Fixture"
            audit = paper / "audit"
            audit.mkdir(parents=True)
            previous_root = EVIDENCE.ROOT
            EVIDENCE.ROOT = root
            self.addCleanup(setattr, EVIDENCE, "ROOT", previous_root)
            payload = self.source_record_payload(corrected=False)
            direct_map = legacy_direct_statement_map(corrected=False)
            (paper / "status.json").write_text(
                json.dumps({"status": "formalized"}), encoding="utf-8"
            )
            (audit / "paper_statement_map.json").write_text(
                json.dumps(direct_map), encoding="utf-8"
            )
            (audit / "source_proof_fidelity.json").write_text(
                json.dumps(fidelity_ledger()), encoding="utf-8"
            )
            payload["paper_statement_map_sha256"] = (
                EVIDENCE.current_paper_statement_map_sha256(paper)
            )
            (audit / "source_record_audit.json").write_text(
                json.dumps(payload), encoding="utf-8"
            )
            (audit / "source_record_match_llm.json").write_text(
                json.dumps(self.source_record_match({})), encoding="utf-8"
            )

            findings = EVIDENCE.source_record_input_target_disposition_findings(
                paper, "formalized"
            )

        self.assertTrue(
            any("no generated direct-route association inventory" in finding.message for finding in findings),
            [finding.message for finding in findings],
        )


class AdministrativeProjectionRebindTests(unittest.TestCase):
    def _validated_context(
        self,
        receipt: dict[str, object],
        raw_audit: dict[str, object],
        raw_bytes: bytes,
        source_map: dict[str, object],
        map_bytes: bytes,
    ) -> tuple[object | None, str]:
        return DISPOSITION.validate_administrative_projection_rebind(
            receipt,
            paper="Fixture",
            raw_audit=raw_audit,
            raw_audit_bytes=raw_bytes,
            raw_audit_relative_path="audit/source_record_audit.json",
            statement_map=source_map,
            statement_map_bytes=map_bytes,
            statement_map_relative_path="audit/paper_statement_map.json",
        )

    def test_rebind_transports_only_the_exact_legacy_to_current_association(self) -> None:
        (
            source_map,
            current_item,
            legacy_item,
            raw_audit,
            receipt,
            raw_bytes,
            map_bytes,
        ) = direct_status_projection_rebind_fixture()
        context, error = self._validated_context(
            receipt, raw_audit, raw_bytes, source_map, map_bytes
        )
        self.assertEqual(error, "")
        self.assertIsNotNone(context)
        transition = receipt["projection_transition"]
        assert isinstance(transition, dict)
        self.assertEqual(transition["legacy_source_item_coverage_digest_schema"], 4)
        self.assertEqual(
            transition["current_source_item_coverage_digest_schema"],
            DISPOSITION.SOURCE_ITEM_COVERAGE_DIGEST_SCHEMA,
        )

        legacy_association = legacy_item["semantic_contract_source_association"]
        assert isinstance(legacy_association, dict)
        response = schema_two_dimension_response(legacy_association, corrected=True)

        without_receipt = DISPOSITION.semantic_target_disposition_errors(
            current_item,
            response,
            statement_map=source_map,
            source_proof_fidelity=fidelity_ledger(),
        )
        self.assertTrue(
            any("semantic_association_sha256" in error for error in without_receipt),
            without_receipt,
        )
        with_receipt = DISPOSITION.semantic_target_disposition_errors(
            current_item,
            response,
            statement_map=source_map,
            source_proof_fidelity=fidelity_ledger(),
            administrative_projection_rebind=context,
        )
        self.assertEqual(with_receipt, [])

        # The repository's semantic provenance gate consumes the same typed
        # context. It must not need to identify the row by a declaration name.
        repository_item = semantic_item()
        repository_item["semantic_contract_source_association"] = current_item[
            "semantic_contract_source_association"
        ]
        findings = REPOSITORY.semantic_model_review_findings(
            "Fixture",
            Path("Fixture"),
            Path("Fixture/audit/source_record_match_llm.json"),
            [repository_item],
            {SEMANTIC_KEY: semantic_judgment(response)},
            digest="current-audit-digest",
            expected_item_digests={},
            severity="ERROR",
            target_disposition_statement_map=source_map,
            target_disposition_source_proof_fidelity=fidelity_ledger(),
            target_disposition_administrative_projection_rebind=context,
            enforce_target_disposition=True,
        )
        self.assertFalse(
            any("invalid source target disposition" in finding.message for finding in findings),
            [finding.message for finding in findings],
        )

    def test_rebind_rejects_every_nonadministrative_drift_and_tampering(self) -> None:
        (
            source_map,
            _current_item,
            _legacy_item,
            raw_audit,
            receipt,
            raw_bytes,
            map_bytes,
        ) = direct_status_projection_rebind_fixture()

        def map_with_change(label: str) -> dict[str, object]:
            changed = deepcopy(source_map)
            item = changed["items"][SOURCE_KEY]
            assert isinstance(item, dict)
            if label == "source_note":
                item["source_note"] = "A materially different source explanation."
            elif label == "target":
                target = item["corrected_target"]
                assert isinstance(target, dict)
                target["statement"] = "A different corrected target."
            elif label == "route":
                item["lean_declarations"] = ["Fixture.Paper.renamed_endpoint"]
            elif label == "nested_source_status":
                model = item["source_model"]
                assert isinstance(model, dict)
                model["source_status"] = "a different mathematical model"
            else:  # pragma: no cover - keeps table edits fail-closed.
                raise AssertionError(label)
            return changed

        for label in ("source_note", "target", "route", "nested_source_status"):
            changed_map = map_with_change(label)
            context, error = self._validated_context(
                receipt,
                raw_audit,
                raw_bytes,
                changed_map,
                json.dumps(changed_map, sort_keys=True).encode("utf-8"),
            )
            self.assertIsNone(context, label)
            self.assertTrue(error, label)

        raw_map_hash_drift = deepcopy(raw_audit)
        semantic_items = raw_map_hash_drift["semantic_model_items"]
        assert isinstance(semantic_items, list) and len(semantic_items) == 1
        association = semantic_items[0]["semantic_contract_source_association"]
        assert isinstance(association, dict)
        identities = association["source_item_identities"]
        assert isinstance(identities, list) and len(identities) == 1
        identities[0]["source_map_item_sha256"] = "0" * 64
        context, error = self._validated_context(
            receipt,
            raw_map_hash_drift,
            json.dumps(raw_map_hash_drift, sort_keys=True).encode("utf-8"),
            source_map,
            map_bytes,
        )
        self.assertIsNone(context)
        self.assertTrue(error)

        altered_legacy_digest = deepcopy(raw_audit)
        semantic_items = altered_legacy_digest["semantic_model_items"]
        assert isinstance(semantic_items, list) and len(semantic_items) == 1
        association = semantic_items[0]["semantic_contract_source_association"]
        assert isinstance(association, dict)
        identities = association["source_item_identities"]
        assert isinstance(identities, list) and len(identities) == 1
        identities[0]["source_semantic_sha256"] = "0" * 64
        context, error = self._validated_context(
            receipt,
            altered_legacy_digest,
            json.dumps(altered_legacy_digest, sort_keys=True).encode("utf-8"),
            source_map,
            map_bytes,
        )
        self.assertIsNone(context)
        self.assertTrue(error)

        tampered_receipt = deepcopy(receipt)
        rebinds = tampered_receipt["association_rebinds"]
        assert isinstance(rebinds, list) and len(rebinds) == 1
        rebinds[0]["association_structure_sha256"] = "0" * 64
        tampered_receipt["receipt_sha256"] = (
            DISPOSITION.administrative_projection_rebind_receipt_digest(
                tampered_receipt
            )
        )
        context, error = self._validated_context(
            tampered_receipt, raw_audit, raw_bytes, source_map, map_bytes
        )
        self.assertIsNone(context)
        self.assertTrue(error)

    def test_rebind_supports_only_the_distinct_schema4_excluded_transition(
        self,
    ) -> None:
        (
            source_map,
            current_item,
            legacy_item,
            raw_audit,
            receipt,
            raw_bytes,
            map_bytes,
        ) = direct_status_projection_rebind_fixture(
            legacy_projection="status_excluded"
        )
        context, error = self._validated_context(
            receipt, raw_audit, raw_bytes, source_map, map_bytes
        )
        self.assertEqual(error, "")
        self.assertIsNotNone(context)
        transition = receipt["projection_transition"]
        assert isinstance(transition, dict)
        self.assertEqual(
            transition["receipt_identity_transition_kinds"],
            ["schema4_direct_source_status_excluded_to_schema5_excluded"],
        )
        legacy_association = legacy_item["semantic_contract_source_association"]
        assert isinstance(legacy_association, dict)
        errors = DISPOSITION.semantic_target_disposition_errors(
            current_item,
            schema_two_dimension_response(legacy_association, corrected=True),
            statement_map=source_map,
            source_proof_fidelity=fidelity_ledger(),
            administrative_projection_rebind=context,
        )
        self.assertEqual(errors, [])

    def test_rebind_refuses_noncanonical_source_status_lookalike(self) -> None:
        """A normalized lookalike is semantic metadata, not a receipt key."""

        source_map = statement_map(corrected=True)
        source_item = source_map["items"][SOURCE_KEY]
        assert isinstance(source_item, dict)
        source_item.update(
            {
                " Source_Status ": "corrected",
                "source_note": "The displayed target has a source correction.",
                "lean_declarations": ["Fixture.Paper.endpoint"],
                "source_model": {"source_status": "finite_carrier_only"},
            }
        )
        current_item = schema_two_semantic_item(SOURCE_KEY, source_item)
        legacy_item = deepcopy(current_item)
        association = legacy_item["semantic_contract_source_association"]
        assert isinstance(association, dict)
        identities = association["source_item_identities"]
        assert isinstance(identities, list) and len(identities) == 1
        identity = identities[0]
        assert isinstance(identity, dict)
        identity["source_semantic_sha256"] = (
            DISPOSITION.legacy_source_item_coverage_sha256_schema4_direct_source_status_excluded(
                source_item, ""
            )
        )
        signature = association["reviewed_elaborated_signature_identity"]
        assert isinstance(signature, dict)
        association["semantic_association_sha256"] = (
            DISPOSITION.semantic_association_record_digest(
                [identity["source_semantic_sha256"]], signature
            )
        )
        raw_audit: dict[str, object] = {
            "paper": "Fixture",
            "source_record_audit_sha256": "e" * 64,
            "semantic_model_items": [legacy_item],
            "boundary_input_items": [],
            "conclusion_dependency_items": [],
            "recursive_field_items": [],
        }
        raw_bytes = json.dumps(raw_audit, sort_keys=True).encode("utf-8")
        map_bytes = json.dumps(source_map, sort_keys=True).encode("utf-8")

        receipt, error = DISPOSITION.build_administrative_projection_rebind(
            paper="Fixture",
            raw_audit=raw_audit,
            raw_audit_bytes=raw_bytes,
            raw_audit_relative_path="audit/source_record_audit.json",
            statement_map=source_map,
            statement_map_bytes=map_bytes,
            statement_map_relative_path="audit/paper_statement_map.json",
        )
        self.assertIsNone(receipt)
        self.assertIn("not an exact direct source_status projection transition", error)

    def test_default_loader_reconstructs_lbg_style_receipt_without_status_config(
        self,
    ) -> None:
        """The canonical path works for schema-4-excluded LBG-style evidence."""

        (
            source_map,
            _current_item,
            _legacy_item,
            raw_audit,
            receipt,
            raw_bytes,
            map_bytes,
        ) = direct_status_projection_rebind_fixture(
            legacy_projection="status_excluded"
        )
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            paper = root / "papers" / "Fixture"
            audit = paper / "audit"
            audit.mkdir(parents=True)
            audit_path = audit / "source_record_audit.json"
            map_path = audit / "paper_statement_map.json"
            receipt_path = audit / DISPOSITION.SOURCE_RECORD_ADMINISTRATIVE_PROJECTION_REBIND_BASENAME
            audit_path.write_bytes(raw_bytes)
            map_path.write_bytes(map_bytes)
            receipt_path.write_text(json.dumps(receipt, sort_keys=True), encoding="utf-8")

            context, loaded_path, error = (
                DISPOSITION.load_administrative_projection_rebind_context(
                    paper="Fixture",
                    paper_dir=paper,
                    raw_audit_path=audit_path,
                    raw_audit=raw_audit,
                    statement_map_path=map_path,
                    statement_map=source_map,
                )
            )
            self.assertEqual(error, "")
            self.assertEqual(loaded_path, receipt_path)
            self.assertIsInstance(
                context, DISPOSITION.ValidatedAdministrativeProjectionRebind
            )

            # The evidence wrapper intentionally takes no rebind path from an
            # empty status configuration; it must reach the same canonical
            # default rather than requiring a status-only special case.
            old_root = EVIDENCE.ROOT
            EVIDENCE.ROOT = root
            try:
                evidence_context, evidence_path, evidence_error = (
                    EVIDENCE.source_record_administrative_projection_rebind_context(
                        paper,
                        {},
                        audit_path=audit_path,
                        audit_payload=raw_audit,
                        statement_map_path=map_path,
                        statement_map=source_map,
                    )
                )
            finally:
                EVIDENCE.ROOT = old_root
            self.assertEqual(evidence_error, "")
            self.assertEqual(evidence_path, receipt_path)
            self.assertIsInstance(
                evidence_context,
                CANONICAL_DISPOSITION.ValidatedAdministrativeProjectionRebind,
            )

    def test_absent_optional_rebind_does_not_require_statement_map(self) -> None:
        """No transport receipt means there are no transport inputs to rebuild."""

        with tempfile.TemporaryDirectory() as temporary:
            paper = Path(temporary) / "papers" / "Fixture"
            audit = paper / "audit"
            audit.mkdir(parents=True)
            audit_path = audit / "source_record_audit.json"
            map_path = audit / "paper_statement_map.json"
            raw_audit: dict[str, object] = {"paper": "Fixture"}

            context, receipt_path, error = (
                DISPOSITION.load_administrative_projection_rebind_context(
                    paper="Fixture",
                    paper_dir=paper,
                    raw_audit_path=audit_path,
                    raw_audit=raw_audit,
                    statement_map_path=map_path,
                    statement_map=None,
                )
            )

        self.assertIsNone(context)
        self.assertEqual(error, "")
        self.assertEqual(
            receipt_path,
            audit
            / DISPOSITION.SOURCE_RECORD_ADMINISTRATIVE_PROJECTION_REBIND_BASENAME,
        )

    def test_conclusion_record_gate_receives_the_same_validated_context(self) -> None:
        """Conclusion provenance cannot invent a separate status exception."""

        (
            source_map,
            _current_item,
            legacy_item,
            raw_audit,
            _receipt,
            _raw_bytes,
            _map_bytes,
        ) = direct_status_projection_rebind_fixture(
            legacy_projection="status_excluded"
        )
        semantic_items = raw_audit["semantic_model_items"]
        assert isinstance(semantic_items, list) and len(semantic_items) == 1
        raw_semantic = semantic_items[0]
        assert isinstance(raw_semantic, dict)
        association = raw_semantic["semantic_contract_source_association"]
        assert isinstance(association, dict)
        declaration = association["reviewed_declaration_identity"]
        signature = association["reviewed_elaborated_signature_identity"]
        assert isinstance(declaration, dict) and isinstance(signature, dict)
        field_key = "Fixture.SourceModel.assumption"
        raw_semantic["reviewed_declaration_identity"] = deepcopy(declaration)
        raw_semantic["reviewed_elaborated_signature_identities"] = [
            deepcopy(signature)
        ]
        raw_semantic["record_input_bindings"] = [
            {"record_roots": ["Fixture.SourceModel"], "binder_names": ["M"]}
        ]
        raw_audit["recursive_field_items"] = [
            {
                "judgment_key": field_key,
                "structure": "Fixture.SourceModel",
                "nested_structures": [],
            }
        ]
        raw_audit["expected_field_judgment_keys"] = [field_key]
        raw_audit["source_proof_fidelity"] = {"model_conventions": []}
        raw_audit["reachable_paper_interface_auxiliary_dependencies"] = []
        raw_audit["ambiguous_reachable_paper_interface_auxiliary_references"] = []
        raw_audit[
            "reachable_paper_interface_auxiliary_quarantine_configuration_errors"
        ] = []
        raw_audit["unresolved_reachable_paper_interface_auxiliaries"] = [
            {"declaration": "Fixture.PaperInterface.opaqueAuxiliary"}
        ]

        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            paper = root / "papers" / "Fixture"
            audit = paper / "audit"
            audit.mkdir(parents=True)
            raw_path = audit / "source_record_audit.json"
            map_path = audit / "paper_statement_map.json"
            raw_bytes = json.dumps(raw_audit, sort_keys=True).encode("utf-8")
            map_bytes = json.dumps(source_map, sort_keys=True).encode("utf-8")
            raw_path.write_bytes(raw_bytes)
            map_path.write_bytes(map_bytes)
            (paper / "status.json").write_text(
                json.dumps({"status": "formalized"}), encoding="utf-8"
            )
            receipt, error = DISPOSITION.build_administrative_projection_rebind(
                paper="Fixture",
                raw_audit=raw_audit,
                raw_audit_bytes=raw_bytes,
                raw_audit_relative_path="audit/source_record_audit.json",
                statement_map=source_map,
                statement_map_bytes=map_bytes,
                statement_map_relative_path="audit/paper_statement_map.json",
            )
            self.assertEqual(error, "")
            assert isinstance(receipt, dict)
            (
                audit / DISPOSITION.SOURCE_RECORD_ADMINISTRATIVE_PROJECTION_REBIND_BASENAME
            ).write_text(json.dumps(receipt, sort_keys=True), encoding="utf-8")

            captured: list[object] = []

            def capture_context(*_args: object, **kwargs: object) -> list[object]:
                captured.append(
                    kwargs.get("target_disposition_administrative_projection_rebind")
                )
                return [object()]

            old_papers = CONCLUSION.PAPERS
            CONCLUSION.PAPERS = root / "papers"
            try:
                with patch.object(
                    CONCLUSION,
                    "semantic_model_review_findings",
                    side_effect=capture_context,
                ):
                    self.assertEqual(
                        CONCLUSION.current_complete_semantic_model_record_bindings(
                            "Fixture",
                            raw_audit,
                            {
                                SEMANTIC_KEY: {"classification": "semantic_model_review"},
                                field_key: {
                                    "classification": "nonpropositional_witness_data"
                                },
                            },
                        ),
                        (),
                    )
            finally:
                CONCLUSION.PAPERS = old_papers
            self.assertEqual(len(captured), 1)
            self.assertIsInstance(
                captured[0],
                CANONICAL_DISPOSITION.ValidatedAdministrativeProjectionRebind,
            )

            class SyntheticRoutingContext:
                """Keep this handoff test independent of raw-routing issuance."""

                def audit_payload_with_authenticated_ledger(
                    self, audit_payload: object
                ) -> tuple[dict[str, object], str]:
                    assert isinstance(audit_payload, dict)
                    return dict(audit_payload), ""

                def quarantine_configuration_errors(self) -> tuple[str, ...]:
                    return ()

                def unresolved_auxiliaries(self) -> tuple[dict[str, object], ...]:
                    return ({"declaration": "Fixture.PaperInterface.opaqueAuxiliary"},)

                def ambiguous_references(self) -> tuple[dict[str, object], ...]:
                    return ()

            with patch.object(
                CONCLUSION,
                "current_auxiliary_routing_context",
                return_value=(SyntheticRoutingContext(), ""),
            ):
                auxiliary_findings = (
                    CONCLUSION.reachable_paper_interface_auxiliary_findings(
                        "Fixture", raw_audit, folder=paper
                    )
                )
            self.assertEqual(len(auxiliary_findings), 1)
            self.assertIn(
                "lexical receipts are diagnostic-only",
                auxiliary_findings[0].message,
            )

    def test_conclusion_rebinds_only_parent_bound_semantic_dimensions(self) -> None:
        """Convention extraction sees a schema-5 pin only after exact transport."""

        (
            source_map,
            _current_item,
            legacy_item,
            raw_audit,
            receipt,
            raw_bytes,
            map_bytes,
        ) = direct_status_projection_rebind_fixture(
            legacy_projection="status_excluded"
        )
        context, error = self._validated_context(
            receipt, raw_audit, raw_bytes, source_map, map_bytes
        )
        self.assertEqual(error, "")
        self.assertIsInstance(context, DISPOSITION.ValidatedAdministrativeProjectionRebind)
        association = legacy_item["semantic_contract_source_association"]
        assert isinstance(association, dict)
        convention = fidelity_ledger()["model_conventions"][0]
        assert isinstance(convention, dict)
        response = {
            "verdict": "matches_approved_source_convention",
            "source_target_disposition": "approved_source_convention",
            "semantic_association_sha256": association[
                "semantic_association_sha256"
            ],
            "model_convention_ids": [CONVENTION_ID],
            "model_convention_sha256_by_id": {
                CONVENTION_ID: DISPOSITION.model_convention_record_digest(convention)
            },
        }
        judgment = {"semantic_model_dimensions": {DIMENSION: response}}
        effective_association = DISPOSITION.administrative_projection_rebound_association(
            association, context
        )
        effective_pin = effective_association["semantic_association_sha256"]
        self.assertIsNone(CONCLUSION._semantic_model_convention_ids(judgment, effective_pin))
        rebound_judgment = (
            CONCLUSION._semantic_model_judgment_with_rebound_dimension_responses(
                judgment,
                association,
                context,
            )
        )
        self.assertEqual(
            CONCLUSION._semantic_model_convention_ids(
                rebound_judgment, effective_pin
            ),
            frozenset({CONVENTION_ID}),
        )

        # A different association cannot advance this response merely because
        # it carries a similarly shaped semantic hash.
        unrelated = deepcopy(association)
        unrelated["reviewed_declaration_identity"]["declaration_sha256"] = "f" * 64
        rebound_unrelated = (
            CONCLUSION._semantic_model_judgment_with_rebound_dimension_responses(
                judgment,
                unrelated,
                context,
            )
        )
        self.assertIsNone(
            CONCLUSION._semantic_model_convention_ids(
                rebound_unrelated, effective_pin
            )
        )

    def test_conclusion_rebinds_only_route_less_field_response_from_parent(
        self,
    ) -> None:
        """A closure field may inherit only its exact semantic parent's pin."""

        (
            source_map,
            current_item,
            legacy_item,
            raw_audit,
            receipt,
            raw_bytes,
            map_bytes,
        ) = direct_status_projection_rebind_fixture(
            legacy_projection="status_excluded"
        )
        context, error = self._validated_context(
            receipt, raw_audit, raw_bytes, source_map, map_bytes
        )
        self.assertEqual(error, "")
        self.assertIsInstance(context, DISPOSITION.ValidatedAdministrativeProjectionRebind)
        legacy_association = legacy_item["semantic_contract_source_association"]
        current_association = current_item["semantic_contract_source_association"]
        assert isinstance(legacy_association, dict)
        assert isinstance(current_association, dict)
        convention = fidelity_ledger()["model_conventions"][0]
        assert isinstance(convention, dict)
        field_judgment = {
            "classification": "approved_source_convention",
            "source_location": "source.tex:9-12",
            "source_target_disposition": "approved_source_convention",
            "semantic_association_sha256": legacy_association[
                "semantic_association_sha256"
            ],
            "model_convention_ids": [CONVENTION_ID],
            "model_convention_sha256_by_id": {
                CONVENTION_ID: DISPOSITION.model_convention_record_digest(convention)
            },
        }
        self.assertTrue(
            CONCLUSION._current_semantic_model_field_is_safe(
                {},
                field_judgment,
                raw_semantic_parent_association=legacy_association,
                semantic_association_sha256=current_association[
                    "semantic_association_sha256"
                ],
                semantic_convention_ids=frozenset({CONVENTION_ID}),
                statement_map=source_map,
                source_proof_fidelity=fidelity_ledger(),
                status="formalized",
                administrative_projection_rebind=context,
            )
        )

        # An independently routed field must remain with its own validation
        # path.  Patch that validator only to observe the response it sees:
        # inheriting the parent transport here would permit a direct route to
        # be silently reclassified.
        captured: list[object] = []

        def reject_direct(
            _field: object, response: object, **_kwargs: object
        ) -> list[str]:
            captured.append(response)
            return ["independent direct route rejected"]

        with patch.object(
            CONCLUSION,
            "approved_source_convention_antecedent_errors",
            side_effect=reject_direct,
        ):
            self.assertFalse(
                CONCLUSION._current_semantic_model_field_is_safe(
                    {"source_contract_association": {}},
                    field_judgment,
                    raw_semantic_parent_association=legacy_association,
                    semantic_association_sha256=current_association[
                        "semantic_association_sha256"
                    ],
                    semantic_convention_ids=frozenset({CONVENTION_ID}),
                    statement_map=source_map,
                    source_proof_fidelity=fidelity_ledger(),
                    status="formalized",
                    administrative_projection_rebind=context,
                )
            )
        self.assertEqual(len(captured), 1)
        self.assertIsInstance(captured[0], dict)
        assert isinstance(captured[0], dict)
        self.assertEqual(
            captured[0]["semantic_association_sha256"],
            legacy_association["semantic_association_sha256"],
        )


if __name__ == "__main__":
    unittest.main()
